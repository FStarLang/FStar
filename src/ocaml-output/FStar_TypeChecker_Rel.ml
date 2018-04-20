open Prims
let (guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> FStar_TypeChecker_Env.guard_t) =
  fun g ->
    {
      FStar_TypeChecker_Env.guard_f = g;
      FStar_TypeChecker_Env.deferred = [];
      FStar_TypeChecker_Env.univ_ineqs = ([], []);
      FStar_TypeChecker_Env.implicits = []
    }
let (guard_form :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun g -> g.FStar_TypeChecker_Env.guard_f
let (is_trivial : FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun g ->
    match g with
    | { FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial;
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
  fun bs ->
    fun g ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let f' =
            FStar_Syntax_Util.abs bs f
              (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0)) in
          let uu___119_91 = g in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___119_91.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___119_91.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___119_91.FStar_TypeChecker_Env.implicits)
          }
let (abstract_guard :
  FStar_Syntax_Syntax.binder ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun b -> fun g -> abstract_guard_n [b] g
let (def_check_vars_in_set :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv FStar_Util.set ->
        FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun rng ->
    fun msg ->
      fun vset ->
        fun t ->
          let uu____114 = FStar_Options.defensive () in
          if uu____114
          then
            let s = FStar_Syntax_Free.names t in
            let uu____118 =
              let uu____119 =
                let uu____120 = FStar_Util.set_difference s vset in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____120 in
              Prims.op_Negation uu____119 in
            (if uu____118
             then
               let uu____125 =
                 let uu____130 =
                   let uu____131 = FStar_Syntax_Print.term_to_string t in
                   let uu____132 =
                     let uu____133 = FStar_Util.set_elements s in
                     FStar_All.pipe_right uu____133
                       (FStar_Syntax_Print.bvs_to_string ",\n\t") in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____131 uu____132 in
                 (FStar_Errors.Warning_Defensive, uu____130) in
               FStar_Errors.log_issue rng uu____125
             else ())
          else ()
let (def_check_closed :
  FStar_Range.range -> Prims.string -> FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun rng ->
    fun msg ->
      fun t ->
        let uu____149 =
          let uu____150 = FStar_Options.defensive () in
          Prims.op_Negation uu____150 in
        if uu____149
        then ()
        else def_check_vars_in_set rng msg FStar_Syntax_Free.empty t
let (def_check_closed_in :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv Prims.list ->
        FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun rng ->
    fun msg ->
      fun l ->
        fun t ->
          let uu____168 =
            let uu____169 = FStar_Options.defensive () in
            Prims.op_Negation uu____169 in
          if uu____168
          then ()
          else
            (let uu____171 = FStar_Util.as_set l FStar_Syntax_Syntax.order_bv in
             def_check_vars_in_set rng msg uu____171 t)
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun rng ->
    fun msg ->
      fun e ->
        fun t ->
          let uu____186 =
            let uu____187 = FStar_Options.defensive () in
            Prims.op_Negation uu____187 in
          if uu____186
          then ()
          else
            (let uu____189 = FStar_TypeChecker_Env.bound_vars e in
             def_check_closed_in rng msg uu____189 t)
let (apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t)
  =
  fun g ->
    fun e ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___120_199 = g in
          let uu____200 =
            let uu____201 =
              let uu____202 =
                let uu____205 =
                  let uu____206 =
                    let uu____221 =
                      let uu____224 = FStar_Syntax_Syntax.as_arg e in
                      [uu____224] in
                    (f, uu____221) in
                  FStar_Syntax_Syntax.Tm_app uu____206 in
                FStar_Syntax_Syntax.mk uu____205 in
              uu____202 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun _0_40 -> FStar_TypeChecker_Common.NonTrivial _0_40)
              uu____201 in
          {
            FStar_TypeChecker_Env.guard_f = uu____200;
            FStar_TypeChecker_Env.deferred =
              (uu___120_199.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___120_199.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___120_199.FStar_TypeChecker_Env.implicits)
          }
let (map_guard :
  FStar_TypeChecker_Env.guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      FStar_TypeChecker_Env.guard_t)
  =
  fun g ->
    fun map1 ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___121_242 = g in
          let uu____243 =
            let uu____244 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____244 in
          {
            FStar_TypeChecker_Env.guard_f = uu____243;
            FStar_TypeChecker_Env.deferred =
              (uu___121_242.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___121_242.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___121_242.FStar_TypeChecker_Env.implicits)
          }
let (trivial : FStar_TypeChecker_Common.guard_formula -> Prims.unit) =
  fun t ->
    match t with
    | FStar_TypeChecker_Common.Trivial -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____248 -> failwith "impossible"
let (conj_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1 ->
    fun g2 ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial, g) -> g
      | (g, FStar_TypeChecker_Common.Trivial) -> g
      | (FStar_TypeChecker_Common.NonTrivial f1,
         FStar_TypeChecker_Common.NonTrivial f2) ->
          let uu____259 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____259
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t ->
    let uu____263 =
      let uu____264 = FStar_Syntax_Util.unmeta t in
      uu____264.FStar_Syntax_Syntax.n in
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
  fun g1 ->
    fun g2 ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial, g) -> g
      | (g, FStar_TypeChecker_Common.Trivial) ->
          FStar_TypeChecker_Common.Trivial
      | (FStar_TypeChecker_Common.NonTrivial f1,
         FStar_TypeChecker_Common.NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2 in check_trivial imp
let (binop_guard :
  (FStar_TypeChecker_Common.guard_formula ->
     FStar_TypeChecker_Common.guard_formula ->
       FStar_TypeChecker_Common.guard_formula)
    ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun f ->
    fun g1 ->
      fun g2 ->
        let uu____299 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
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
  = fun g1 -> fun g2 -> binop_guard conj_guard_f g1 g2
let (imp_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun g1 -> fun g2 -> binop_guard imp_guard_f g1 g2
let (close_guard_univs :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun us ->
    fun bs ->
      fun g ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let f1 =
              FStar_List.fold_right2
                (fun u ->
                   fun b ->
                     fun f1 ->
                       let uu____366 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____366
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___122_368 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___122_368.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___122_368.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___122_368.FStar_TypeChecker_Env.implicits)
            }
let (close_forall :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binder Prims.list ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env ->
    fun bs ->
      fun f ->
        FStar_List.fold_right
          (fun b ->
             fun f1 ->
               let uu____387 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____387
               then f1
               else
                 (let u =
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
let (close_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env ->
    fun binders ->
      fun g ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___123_400 = g in
            let uu____401 =
              let uu____402 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____402 in
            {
              FStar_TypeChecker_Env.guard_f = uu____401;
              FStar_TypeChecker_Env.deferred =
                (uu___123_400.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___123_400.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___123_400.FStar_TypeChecker_Env.implicits)
            }
let (new_uvar :
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2)
  =
  fun r ->
    fun binders ->
      fun k ->
        let uv = FStar_Syntax_Unionfind.fresh () in
        match binders with
        | [] ->
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k))
                FStar_Pervasives_Native.None r in
            (uv1, uv1)
        | uu____432 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____457 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____457 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r in
            let uu____465 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                FStar_Pervasives_Native.None r in
            (uu____465, uv1)
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar, FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,
  FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar, FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee ->
    match projectee with | TERM _0 -> true | uu____512 -> false
let (__proj__TERM__item___0 :
  uvi ->
    ((FStar_Syntax_Syntax.uvar, FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,
      FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | TERM _0 -> _0
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee ->
    match projectee with | UNIV _0 -> true | uu____552 -> false
let (__proj__UNIV__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.universe_uvar, FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | UNIV _0 -> _0
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int, Prims.string, FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list
    ;
  ctr: Prims.int ;
  defer_ok: Prims.bool ;
  smt_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env }[@@deriving show]
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__attempting
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int, Prims.string, FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun projectee ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__wl_deferred
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} -> __fname__ctr
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__defer_ok
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__smt_ok
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} -> __fname__tcenv
type solution =
  | Success of FStar_TypeChecker_Common.deferred 
  | Failed of (FStar_TypeChecker_Common.prob, Prims.string)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee ->
    match projectee with | Success _0 -> true | uu____738 -> false
let (__proj__Success__item___0 :
  solution -> FStar_TypeChecker_Common.deferred) =
  fun projectee -> match projectee with | Success _0 -> _0
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee ->
    match projectee with | Failed _0 -> true | uu____754 -> false
let (__proj__Failed__item___0 :
  solution ->
    (FStar_TypeChecker_Common.prob, Prims.string)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | Failed _0 -> _0
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT [@@deriving show]
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee ->
    match projectee with | COVARIANT -> true | uu____777 -> false
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee ->
    match projectee with | CONTRAVARIANT -> true | uu____781 -> false
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee ->
    match projectee with | INVARIANT -> true | uu____785 -> false
type tprob =
  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem[@@deriving show]
type cprob =
  (FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem
[@@deriving show]
type ('a, 'b) problem_t = ('a, 'b) FStar_TypeChecker_Common.problem[@@deriving
                                                                    show]
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___89_808 ->
    match uu___89_808 with
    | FStar_TypeChecker_Common.EQ -> "="
    | FStar_TypeChecker_Common.SUB -> "<:"
    | FStar_TypeChecker_Common.SUBINV -> ":>"
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t ->
    let compact = FStar_Syntax_Print.term_to_string t in
    let detail =
      let uu____814 =
        let uu____815 = FStar_Syntax_Subst.compress t in
        uu____815.FStar_Syntax_Syntax.n in
      match uu____814 with
      | FStar_Syntax_Syntax.Tm_uvar (u, t1) ->
          let uu____844 = FStar_Syntax_Print.uvar_to_string u in
          let uu____845 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.format2 "%s : %s" uu____844 uu____845
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u, ty);
             FStar_Syntax_Syntax.pos = uu____848;
             FStar_Syntax_Syntax.vars = uu____849;_},
           args)
          ->
          let uu____895 = FStar_Syntax_Print.uvar_to_string u in
          let uu____896 = FStar_Syntax_Print.term_to_string ty in
          let uu____897 = FStar_Syntax_Print.args_to_string args in
          FStar_Util.format3 "(%s : %s) %s" uu____895 uu____896 uu____897
      | uu____898 -> "--" in
    let uu____899 = FStar_Syntax_Print.tag_of_term t in
    FStar_Util.format3 "%s (%s)\t%s" compact uu____899 detail
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env ->
    fun uu___90_905 ->
      match uu___90_905 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____911 =
            let uu____914 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____915 =
              let uu____918 = term_to_string p.FStar_TypeChecker_Common.lhs in
              let uu____919 =
                let uu____922 =
                  let uu____925 =
                    term_to_string p.FStar_TypeChecker_Common.rhs in
                  [uu____925] in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____922 in
              uu____918 :: uu____919 in
            uu____914 :: uu____915 in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____911
      | FStar_TypeChecker_Common.CProb p ->
          let uu____931 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____932 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____933 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____931 uu____932
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____933
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env ->
    fun uu___91_939 ->
      match uu___91_939 with
      | UNIV (u, t) ->
          let x =
            let uu____943 = FStar_Options.hide_uvar_nums () in
            if uu____943
            then "?"
            else
              (let uu____945 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____945 FStar_Util.string_of_int) in
          let uu____946 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____946
      | TERM ((u, uu____948), t) ->
          let x =
            let uu____955 = FStar_Options.hide_uvar_nums () in
            if uu____955
            then "?"
            else
              (let uu____957 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____957 FStar_Util.string_of_int) in
          let uu____958 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____958
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env ->
    fun uvis ->
      let uu____969 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____969 (FStar_String.concat ", ")
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms ->
    let uu____981 =
      let uu____984 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____984
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____981 (FStar_String.concat ", ")
let args_to_string :
  'Auu____995 .
    (FStar_Syntax_Syntax.term, 'Auu____995) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args ->
    let uu____1012 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1030 ->
              match uu____1030 with
              | (x, uu____1036) -> FStar_Syntax_Print.term_to_string x)) in
    FStar_All.pipe_right uu____1012 (FStar_String.concat " ")
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env ->
    let uu____1042 =
      let uu____1043 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____1043 in
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
  fun env ->
    fun prob ->
      fun smt_ok ->
        let uu___124_1059 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___124_1059.wl_deferred);
          ctr = (uu___124_1059.ctr);
          defer_ok = (uu___124_1059.defer_ok);
          smt_ok;
          tcenv = (uu___124_1059.tcenv)
        }
let (singleton :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist) =
  fun env -> fun prob -> singleton' env prob true
let wl_of_guard :
  'Auu____1069 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1069, FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env ->
    fun g ->
      let uu___125_1090 = empty_worklist env in
      let uu____1091 = FStar_List.map FStar_Pervasives_Native.snd g in
      {
        attempting = uu____1091;
        wl_deferred = (uu___125_1090.wl_deferred);
        ctr = (uu___125_1090.ctr);
        defer_ok = false;
        smt_ok = (uu___125_1090.smt_ok);
        tcenv = (uu___125_1090.tcenv)
      }
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason ->
    fun prob ->
      fun wl ->
        let uu___126_1105 = wl in
        {
          attempting = (uu___126_1105.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___126_1105.ctr);
          defer_ok = (uu___126_1105.defer_ok);
          smt_ok = (uu___126_1105.smt_ok);
          tcenv = (uu___126_1105.tcenv)
        }
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs ->
    fun wl ->
      let uu___127_1122 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___127_1122.wl_deferred);
        ctr = (uu___127_1122.ctr);
        defer_ok = (uu___127_1122.defer_ok);
        smt_ok = (uu___127_1122.smt_ok);
        tcenv = (uu___127_1122.tcenv)
      }
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env ->
    fun reason ->
      fun prob ->
        (let uu____1133 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____1133
         then
           let uu____1134 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1134
         else ());
        Failed (prob, reason)
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___92_1138 ->
    match uu___92_1138 with
    | FStar_TypeChecker_Common.EQ -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV -> FStar_TypeChecker_Common.SUB
let invert :
  'Auu____1142 'Auu____1143 .
    ('Auu____1142, 'Auu____1143) FStar_TypeChecker_Common.problem ->
      ('Auu____1142, 'Auu____1143) FStar_TypeChecker_Common.problem
  =
  fun p ->
    let uu___128_1160 = p in
    {
      FStar_TypeChecker_Common.pid =
        (uu___128_1160.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___128_1160.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___128_1160.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___128_1160.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___128_1160.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___128_1160.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___128_1160.FStar_TypeChecker_Common.rank)
    }
let maybe_invert :
  'Auu____1168 'Auu____1169 .
    ('Auu____1168, 'Auu____1169) FStar_TypeChecker_Common.problem ->
      ('Auu____1168, 'Auu____1169) FStar_TypeChecker_Common.problem
  =
  fun p ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___93_1189 ->
    match uu___93_1189 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41 -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42 -> FStar_TypeChecker_Common.CProb _0_42)
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel ->
    fun uu___94_1213 ->
      match uu___94_1213 with
      | INVARIANT -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT -> invert_rel rel
      | COVARIANT -> rel
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___95_1216 ->
    match uu___95_1216 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___96_1229 ->
    match uu___96_1229 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___97_1244 ->
    match uu___97_1244 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___98_1259 ->
    match uu___98_1259 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let (p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___99_1276 ->
    match uu___99_1276 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let def_scope_wf :
  'Auu____1295 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv, 'Auu____1295) FStar_Pervasives_Native.tuple2
          Prims.list -> Prims.unit
  =
  fun msg ->
    fun rng ->
      fun r ->
        let uu____1320 =
          let uu____1321 = FStar_Options.defensive () in
          Prims.op_Negation uu____1321 in
        if uu____1320
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv, uu____1351)::bs ->
                 (def_check_closed_in rng msg prev
                    bv.FStar_Syntax_Syntax.sort;
                  aux (FStar_List.append prev [bv]) bs) in
           aux [] r)
let (p_scope : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders)
  =
  fun prob ->
    let r =
      match prob with
      | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
      | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope in
    def_scope_wf "p_scope" (p_loc prob) r; r
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun msg ->
    fun prob ->
      fun phi ->
        let uu____1388 =
          let uu____1389 = FStar_Options.defensive () in
          Prims.op_Negation uu____1389 in
        if uu____1388
        then ()
        else
          (let uu____1391 =
             let uu____1394 = p_scope prob in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1394 in
           def_check_closed_in (p_loc prob) msg uu____1391 phi)
let (def_check_prob :
  Prims.string -> FStar_TypeChecker_Common.prob -> Prims.unit) =
  fun msg ->
    fun prob ->
      (let uu____1420 =
         let uu____1421 = FStar_Options.defensive () in
         Prims.op_Negation uu____1421 in
       if uu____1420
       then ()
       else
         (let uu____1423 = p_scope prob in
          def_scope_wf (Prims.strcat msg ".scope") (p_loc prob) uu____1423));
      (let uu____1431 =
         FStar_All.pipe_left FStar_Pervasives_Native.fst (p_guard prob) in
       def_check_scoped (Prims.strcat msg ".guard") prob uu____1431);
      (let uu____1437 =
         FStar_All.pipe_left FStar_Pervasives_Native.snd (p_guard prob) in
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
  fun prob ->
    fun t1 ->
      fun t2 ->
        let uu____1463 = FStar_Syntax_Util.type_u () in
        match uu____1463 with
        | (t_type, u) ->
            let uu____1470 =
              let uu____1475 = p_scope prob in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____1475 t_type in
            (match uu____1470 with
             | (tt, uu____1477) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___100_1480 ->
    match uu___100_1480 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_43 -> FStar_TypeChecker_Common.TProb _0_43) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_44 -> FStar_TypeChecker_Common.CProb _0_44) (invert p)
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p ->
    let uu____1502 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1502 = (Prims.parse_int "1")
let (next_pid : Prims.unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1514 -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr
let mk_problem :
  'Auu____1725 'Auu____1726 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1725 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1725 ->
              'Auu____1726 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1725, 'Auu____1726)
                    FStar_TypeChecker_Common.problem
  =
  fun scope ->
    fun orig ->
      fun lhs ->
        fun rel ->
          fun rhs ->
            fun elt ->
              fun reason ->
                let uu____1763 = next_pid () in
                let uu____1764 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1763;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1764;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let new_problem :
  'Auu____1778 'Auu____1779 .
    FStar_TypeChecker_Env.env ->
      'Auu____1778 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1778 ->
            'Auu____1779 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1778, 'Auu____1779)
                    FStar_TypeChecker_Common.problem
  =
  fun env ->
    fun lhs ->
      fun rel ->
        fun rhs ->
          fun elt ->
            fun loc ->
              fun reason ->
                let scope = FStar_TypeChecker_Env.all_binders env in
                let uu____1817 = next_pid () in
                let uu____1818 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1817;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1818;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let problem_using_guard :
  'Auu____1831 'Auu____1832 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1831 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1831 ->
            'Auu____1832 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1831, 'Auu____1832) FStar_TypeChecker_Common.problem
  =
  fun orig ->
    fun lhs ->
      fun rel ->
        fun rhs ->
          fun elt ->
            fun reason ->
              let uu____1865 = next_pid () in
              let uu____1866 = p_scope orig in
              {
                FStar_TypeChecker_Common.pid = uu____1865;
                FStar_TypeChecker_Common.lhs = lhs;
                FStar_TypeChecker_Common.relation = rel;
                FStar_TypeChecker_Common.rhs = rhs;
                FStar_TypeChecker_Common.element = elt;
                FStar_TypeChecker_Common.logical_guard = (p_guard orig);
                FStar_TypeChecker_Common.scope = uu____1866;
                FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
                FStar_TypeChecker_Common.loc = (p_loc orig);
                FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
              }
let guard_on_element :
  'Auu____1872 .
    worklist ->
      ('Auu____1872, FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
        FStar_TypeChecker_Common.problem ->
        FStar_Syntax_Syntax.bv ->
          FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun wl ->
    fun problem ->
      fun x ->
        fun phi ->
          match problem.FStar_TypeChecker_Common.element with
          | FStar_Pervasives_Native.None ->
              let u =
                (wl.tcenv).FStar_TypeChecker_Env.universe_of wl.tcenv
                  x.FStar_Syntax_Syntax.sort in
              FStar_Syntax_Util.mk_forall u x phi
          | FStar_Pervasives_Native.Some e ->
              FStar_Syntax_Subst.subst [FStar_Syntax_Syntax.NT (x, e)] phi
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env ->
    fun d ->
      fun s ->
        let uu____1922 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1922
        then
          let uu____1923 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1924 = prob_to_string env d in
          let uu____1925 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1923 uu____1924 uu____1925 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ -> "equal to"
             | FStar_TypeChecker_Common.SUB -> "a subtype of"
             | uu____1931 -> failwith "impossible" in
           let uu____1932 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1946 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1947 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1946, uu____1947)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1953 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1954 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1953, uu____1954) in
           match uu____1932 with
           | (lhs, rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let (commit : uvi Prims.list -> Prims.unit) =
  fun uvis ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___101_1970 ->
            match uu___101_1970 with
            | UNIV (u, t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1982 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u, uu____1984), t) ->
                (def_check_closed t.FStar_Syntax_Syntax.pos "commit" t;
                 FStar_Syntax_Util.set_uvar u t)))
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv ->
    fun s ->
      FStar_Util.find_map s
        (fun uu___102_2005 ->
           match uu___102_2005 with
           | UNIV uu____2008 -> FStar_Pervasives_Native.None
           | TERM ((u, uu____2014), t) ->
               let uu____2020 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____2020
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
let (find_univ_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u ->
    fun s ->
      FStar_Util.find_map s
        (fun uu___103_2040 ->
           match uu___103_2040 with
           | UNIV (u', t) ->
               let uu____2045 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____2045
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2049 -> FStar_Pervasives_Native.None)
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu____2056 =
        let uu____2057 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2057 in
      FStar_Syntax_Subst.compress uu____2056
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu____2064 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____2064
let norm_arg :
  'Auu____2068 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term, 'Auu____2068) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term, 'Auu____2068)
          FStar_Pervasives_Native.tuple2
  =
  fun env ->
    fun t ->
      let uu____2089 = sn env (FStar_Pervasives_Native.fst t) in
      (uu____2089, (FStar_Pervasives_Native.snd t))
let (sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun env ->
    fun binders ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____2120 ->
              match uu____2120 with
              | (x, imp) ->
                  let uu____2131 =
                    let uu___129_2132 = x in
                    let uu____2133 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___129_2132.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___129_2132.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2133
                    } in
                  (uu____2131, imp)))
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl ->
    fun u ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2148 = aux u3 in FStar_Syntax_Syntax.U_succ uu____2148
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2152 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____2152
        | uu____2155 -> u2 in
      let uu____2156 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2156
let (base_and_refinement_maybe_delta :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
          (FStar_Syntax_Syntax.bv,
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2)
  =
  fun should_delta ->
    fun env ->
      fun t1 ->
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
              FStar_TypeChecker_Normalize.HNF] in
          FStar_TypeChecker_Normalize.normalize_refinement steps env1 t in
        let rec aux norm1 t11 =
          let t12 = FStar_Syntax_Util.unmeta t11 in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____2268 = norm_refinement env t12 in
                 match uu____2268 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1, phi1);
                     FStar_Syntax_Syntax.pos = uu____2285;
                     FStar_Syntax_Syntax.vars = uu____2286;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2312 =
                       let uu____2313 = FStar_Syntax_Print.term_to_string tt in
                       let uu____2314 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2313 uu____2314 in
                     failwith uu____2312)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____2330 = FStar_Syntax_Util.unfold_lazy i in
              aux norm1 uu____2330
          | FStar_Syntax_Syntax.Tm_uinst uu____2331 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____2368 =
                   let uu____2369 = FStar_Syntax_Subst.compress t1' in
                   uu____2369.FStar_Syntax_Syntax.n in
                 match uu____2368 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2386 -> aux true t1'
                 | uu____2393 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2408 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____2439 =
                   let uu____2440 = FStar_Syntax_Subst.compress t1' in
                   uu____2440.FStar_Syntax_Syntax.n in
                 match uu____2439 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2457 -> aux true t1'
                 | uu____2464 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2479 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____2524 =
                   let uu____2525 = FStar_Syntax_Subst.compress t1' in
                   uu____2525.FStar_Syntax_Syntax.n in
                 match uu____2524 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2542 -> aux true t1'
                 | uu____2549 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2564 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2579 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2594 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2609 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2624 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2651 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____2682 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2703 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2734 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2761 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2798 ->
              let uu____2805 =
                let uu____2806 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2807 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2806 uu____2807 in
              failwith uu____2805
          | FStar_Syntax_Syntax.Tm_ascribed uu____2822 ->
              let uu____2849 =
                let uu____2850 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2851 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2850 uu____2851 in
              failwith uu____2849
          | FStar_Syntax_Syntax.Tm_delayed uu____2866 ->
              let uu____2891 =
                let uu____2892 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2893 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2892 uu____2893 in
              failwith uu____2891
          | FStar_Syntax_Syntax.Tm_unknown ->
              let uu____2908 =
                let uu____2909 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2910 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2909 uu____2910 in
              failwith uu____2908 in
        let uu____2925 = whnf env t1 in aux false uu____2925
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,
        (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env -> fun t -> base_and_refinement_maybe_delta false env t
let normalize_refinement :
  'Auu____2947 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____2947 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun steps ->
    fun env ->
      fun wl ->
        fun t0 ->
          FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let (unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env ->
    fun t ->
      let uu____2970 = base_and_refinement env t in
      FStar_All.pipe_right uu____2970 FStar_Pervasives_Native.fst
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t ->
    let uu____3004 = FStar_Syntax_Syntax.null_bv t in
    (uu____3004, FStar_Syntax_Util.t_true)
let as_refinement :
  'Auu____3010 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3010 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1 ->
    fun env ->
      fun wl ->
        fun t ->
          let uu____3031 = base_and_refinement_maybe_delta delta1 env t in
          match uu____3031 with
          | (t_base, refinement) ->
              (match refinement with
               | FStar_Pervasives_Native.None -> trivial_refinement t_base
               | FStar_Pervasives_Native.Some (x, phi) -> (x, phi))
let (force_refinement :
  (FStar_Syntax_Syntax.term,
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun uu____3110 ->
    match uu____3110 with
    | (t_base, refopt) ->
        let uu____3137 =
          match refopt with
          | FStar_Pervasives_Native.Some (y, phi) -> (y, phi)
          | FStar_Pervasives_Native.None -> trivial_refinement t_base in
        (match uu____3137 with
         | (y, phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl -> fun prob -> prob_to_string wl.tcenv prob
let (wl_to_string : worklist -> Prims.string) =
  fun wl ->
    let uu____3169 =
      let uu____3172 =
        let uu____3175 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3198 ->
                  match uu____3198 with | (uu____3205, uu____3206, x) -> x)) in
        FStar_List.append wl.attempting uu____3175 in
      FStar_List.map (wl_prob_to_string wl) uu____3172 in
    FStar_All.pipe_right uu____3169 (FStar_String.concat "\n\t")
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k ->
    fun ys ->
      fun t ->
        let uu____3219 =
          let uu____3232 =
            let uu____3233 = FStar_Syntax_Subst.compress k in
            uu____3233.FStar_Syntax_Syntax.n in
          match uu____3232 with
          | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3286 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____3286)
              else
                (let uu____3300 = FStar_Syntax_Util.abs_formals t in
                 match uu____3300 with
                 | (ys', t1, uu____3323) ->
                     let uu____3328 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3328))
          | uu____3369 ->
              let uu____3370 =
                let uu____3381 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3381) in
              ((ys, t), uu____3370) in
        match uu____3219 with
        | ((ys1, t1), (xs, c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (FStar_Pervasives_Native.Some
                   (FStar_Syntax_Util.mk_residual_comp
                      FStar_Parser_Const.effect_Tot_lid
                      FStar_Pervasives_Native.None []))
            else
              (let c1 =
                 let uu____3430 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3430 c in
               FStar_Syntax_Util.abs ys1 t1
                 (FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_comp_of_comp c1)))
let (solve_prob' :
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        uvi Prims.list -> worklist -> worklist)
  =
  fun resolve_ok ->
    fun prob ->
      fun logical_guard ->
        fun uvis ->
          fun wl ->
            def_check_prob "solve_prob'" prob;
            (let phi =
               match logical_guard with
               | FStar_Pervasives_Native.None -> FStar_Syntax_Util.t_true
               | FStar_Pervasives_Native.Some phi -> phi in
             let uu____3459 = p_guard prob in
             match uu____3459 with
             | (uu____3464, uv) ->
                 ((let uu____3467 =
                     let uu____3468 = FStar_Syntax_Subst.compress uv in
                     uu____3468.FStar_Syntax_Syntax.n in
                   match uu____3467 with
                   | FStar_Syntax_Syntax.Tm_uvar (uvar, k) ->
                       let bs = p_scope prob in
                       let phi1 = u_abs k bs phi in
                       ((let uu____3500 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug wl.tcenv)
                             (FStar_Options.Other "Rel") in
                         if uu____3500
                         then
                           let uu____3501 =
                             FStar_Util.string_of_int (p_pid prob) in
                           let uu____3502 =
                             FStar_Syntax_Print.term_to_string uv in
                           let uu____3503 =
                             FStar_Syntax_Print.term_to_string phi1 in
                           FStar_Util.print3
                             "Solving %s (%s) with formula %s\n" uu____3501
                             uu____3502 uu____3503
                         else ());
                        def_check_closed (p_loc prob) "solve_prob'" phi1;
                        FStar_Syntax_Util.set_uvar uvar phi1)
                   | uu____3506 ->
                       if Prims.op_Negation resolve_ok
                       then
                         failwith
                           "Impossible: this instance has already been assigned a solution"
                       else ());
                  commit uvis;
                  (let uu___130_3509 = wl in
                   {
                     attempting = (uu___130_3509.attempting);
                     wl_deferred = (uu___130_3509.wl_deferred);
                     ctr = (wl.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___130_3509.defer_ok);
                     smt_ok = (uu___130_3509.smt_ok);
                     tcenv = (uu___130_3509.tcenv)
                   })))
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid ->
    fun sol ->
      fun wl ->
        (let uu____3524 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3524
         then
           let uu____3525 = FStar_Util.string_of_int pid in
           let uu____3526 =
             let uu____3527 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3527 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3525 uu____3526
         else ());
        commit sol;
        (let uu___131_3534 = wl in
         {
           attempting = (uu___131_3534.attempting);
           wl_deferred = (uu___131_3534.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___131_3534.defer_ok);
           smt_ok = (uu___131_3534.smt_ok);
           tcenv = (uu___131_3534.tcenv)
         })
let (solve_prob :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      uvi Prims.list -> worklist -> worklist)
  =
  fun prob ->
    fun logical_guard ->
      fun uvis ->
        fun wl ->
          def_check_prob "solve_prob.prob" prob;
          FStar_Util.iter_opt logical_guard
            (def_check_scoped "solve_prob.guard" prob);
          (let conj_guard1 t g =
             match (t, g) with
             | (uu____3574, FStar_TypeChecker_Common.Trivial) -> t
             | (FStar_Pervasives_Native.None,
                FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some t1,
                FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____3586 = FStar_Syntax_Util.mk_conj t1 f in
                 FStar_Pervasives_Native.Some uu____3586 in
           (let uu____3592 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "RelCheck") in
            if uu____3592
            then
              let uu____3593 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
              let uu____3594 =
                let uu____3595 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
                FStar_All.pipe_right uu____3595 (FStar_String.concat ", ") in
              FStar_Util.print2 "Solving %s: with %s\n" uu____3593 uu____3594
            else ());
           solve_prob' false prob logical_guard uvis wl)
let rec occurs :
  'b .
    worklist ->
      (FStar_Syntax_Syntax.uvar, 'b) FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun wl ->
    fun uk ->
      fun t ->
        let uu____3627 =
          let uu____3634 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3634 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3627
          (FStar_Util.for_some
             (fun uu____3670 ->
                match uu____3670 with
                | (uv, uu____3676) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check :
  'Auu____3683 'Auu____3684 .
    'Auu____3683 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar, 'Auu____3684)
          FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.typ ->
            (Prims.bool, Prims.string FStar_Pervasives_Native.option)
              FStar_Pervasives_Native.tuple2
  =
  fun env ->
    fun wl ->
      fun uk ->
        fun t ->
          let occurs_ok =
            let uu____3716 = occurs wl uk t in Prims.op_Negation uu____3716 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3723 =
                 let uu____3724 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3725 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3724 uu____3725 in
               FStar_Pervasives_Native.Some uu____3723) in
          (occurs_ok, msg)
let occurs_and_freevars_check :
  'Auu____3735 'Auu____3736 .
    'Auu____3735 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar, 'Auu____3736)
          FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.bv FStar_Util.set ->
            FStar_Syntax_Syntax.term ->
              (Prims.bool, Prims.bool,
                (Prims.string FStar_Pervasives_Native.option,
                  FStar_Syntax_Syntax.bv FStar_Util.set,
                  FStar_Syntax_Syntax.bv FStar_Util.set)
                  FStar_Pervasives_Native.tuple3)
                FStar_Pervasives_Native.tuple3
  =
  fun env ->
    fun wl ->
      fun uk ->
        fun fvs ->
          fun t ->
            let fvs_t = FStar_Syntax_Free.names t in
            let uu____3790 = occurs_check env wl uk t in
            match uu____3790 with
            | (occurs_ok, msg) ->
                let uu____3821 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3821, (msg, fvs, fvs_t))
let intersect_vars :
  'Auu____3844 'Auu____3845 .
    (FStar_Syntax_Syntax.bv, 'Auu____3844) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv, 'Auu____3845) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv, 'Auu____3845) FStar_Pervasives_Native.tuple2
          Prims.list
  =
  fun v1 ->
    fun v2 ->
      let as_set1 v3 =
        FStar_All.pipe_right v3
          (FStar_List.fold_left
             (fun out ->
                fun x ->
                  FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
             FStar_Syntax_Syntax.no_names) in
      let v1_set = as_set1 v1 in
      let uu____3929 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3983 ->
                fun uu____3984 ->
                  match (uu____3983, uu____3984) with
                  | ((isect, isect_set), (x, imp)) ->
                      let uu____4065 =
                        let uu____4066 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____4066 in
                      if uu____4065
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____4091 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____4091
                         then
                           let uu____4104 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____4104)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3929 with | (isect, uu____4145) -> FStar_List.rev isect
let binders_eq :
  'Auu____4170 'Auu____4171 .
    (FStar_Syntax_Syntax.bv, 'Auu____4170) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv, 'Auu____4171) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1 ->
    fun v2 ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4226 ->
              fun uu____4227 ->
                match (uu____4226, uu____4227) with
                | ((a, uu____4245), (b, uu____4247)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt :
  'Auu____4261 'Auu____4262 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv, 'Auu____4261) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term, 'Auu____4262)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv, 'Auu____4262)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env ->
    fun seen ->
      fun arg ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4313 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4327 ->
                      match uu____4327 with
                      | (b, uu____4333) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____4313
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4349 -> FStar_Pervasives_Native.None
let rec (pat_vars :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun env ->
    fun seen ->
      fun args ->
        match args with
        | [] -> FStar_Pervasives_Native.Some (FStar_List.rev seen)
        | hd1::rest ->
            let uu____4422 = pat_var_opt env seen hd1 in
            (match uu____4422 with
             | FStar_Pervasives_Native.None ->
                 ((let uu____4436 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4436
                   then
                     let uu____4437 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4437
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____4455 =
      let uu____4456 = FStar_Syntax_Subst.compress t in
      uu____4456.FStar_Syntax_Syntax.n in
    match uu____4455 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4459 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4476;
           FStar_Syntax_Syntax.pos = uu____4477;
           FStar_Syntax_Syntax.vars = uu____4478;_},
         uu____4479)
        -> true
    | uu____4516 -> false
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
         FStar_Pervasives_Native.option FStar_Unionfind.p_uvar,
        FStar_Syntax_Syntax.version) FStar_Pervasives_Native.tuple2,
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
        FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple4)
  =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv, k) -> (t, uv, k, [])
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k);
           FStar_Syntax_Syntax.pos = uu____4640;
           FStar_Syntax_Syntax.vars = uu____4641;_},
         args)
        -> (t, uv, k, args)
    | uu____4709 -> failwith "Not a flex-uvar"
let (destruct_flex_pattern :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
         (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
            FStar_Pervasives_Native.option FStar_Unionfind.p_uvar,
           FStar_Syntax_Syntax.version) FStar_Pervasives_Native.tuple2,
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
         (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
           FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
           Prims.list)
         FStar_Pervasives_Native.tuple4,
        FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun t ->
      let uu____4786 = destruct_flex_t t in
      match uu____4786 with
      | (t1, uv, k, args) ->
          let uu____4901 = pat_vars env [] args in
          (match uu____4901 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4999 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,
  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch 
  | FullMatch [@@deriving show]
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | MisMatch _0 -> true | uu____5080 -> false
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | MisMatch _0 -> _0
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | HeadMatch -> true | uu____5115 -> false
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | FullMatch -> true | uu____5119 -> false
let string_of_option :
  'Auu____5123 .
    ('Auu____5123 -> Prims.string) ->
      'Auu____5123 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f ->
    fun uu___104_5136 ->
      match uu___104_5136 with
      | FStar_Pervasives_Native.None -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____5142 = f x in Prims.strcat "Some " uu____5142
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___105_5145 ->
    match uu___105_5145 with
    | MisMatch (d1, d2) ->
        let uu____5156 =
          let uu____5157 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1 in
          let uu____5158 =
            let uu____5159 =
              let uu____5160 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2 in
              Prims.strcat uu____5160 ")" in
            Prims.strcat ") (" uu____5159 in
          Prims.strcat uu____5157 uu____5158 in
        Prims.strcat "MisMatch (" uu____5156
    | HeadMatch -> "HeadMatch"
    | FullMatch -> "FullMatch"
let (head_match : match_result -> match_result) =
  fun uu___106_5163 ->
    match uu___106_5163 with
    | MisMatch (i, j) -> MisMatch (i, j)
    | uu____5178 -> HeadMatch
let (and_match :
  match_result -> (Prims.unit -> match_result) -> match_result) =
  fun m1 ->
    fun m2 ->
      match m1 with
      | MisMatch (i, j) -> MisMatch (i, j)
      | HeadMatch ->
          let uu____5204 = m2 () in
          (match uu____5204 with
           | MisMatch (i, j) -> MisMatch (i, j)
           | uu____5219 -> HeadMatch)
      | FullMatch -> m2 ()
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env ->
    fun fv ->
      match fv.FStar_Syntax_Syntax.fv_delta with
      | FStar_Syntax_Syntax.Delta_abstract d ->
          if
            ((env.FStar_TypeChecker_Env.curmodule).FStar_Ident.str =
               ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr)
              && (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
          then d
          else FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5228 ->
          let uu____5229 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____5229 with
           | FStar_Pervasives_Native.None ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5240 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec (delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____5259 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5268 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5296 = FStar_Syntax_Util.unfold_lazy i in
          delta_depth_of_term env uu____5296
      | FStar_Syntax_Syntax.Tm_unknown -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5297 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5298 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5299 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5316 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5329 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2, uu____5353) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____5359, uu____5360) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2, uu____5402) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5423;
             FStar_Syntax_Syntax.index = uu____5424;
             FStar_Syntax_Syntax.sort = t2;_},
           uu____5426)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5433 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5434 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5435 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____5448 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5455 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5473 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5473
let rec (head_matches :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> match_result)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let t11 = FStar_Syntax_Util.unmeta t1 in
        let t21 = FStar_Syntax_Util.unmeta t2 in
        match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Tm_name x, FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f, FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____5494 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5494
            then FullMatch
            else
              (let uu____5496 =
                 let uu____5505 =
                   let uu____5508 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5508 in
                 let uu____5509 =
                   let uu____5512 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5512 in
                 (uu____5505, uu____5509) in
               MisMatch uu____5496)
        | (FStar_Syntax_Syntax.Tm_uinst (f, uu____5518),
           FStar_Syntax_Syntax.Tm_uinst (g, uu____5520)) ->
            let uu____5529 = head_matches env f g in
            FStar_All.pipe_right uu____5529 head_match
        | (FStar_Syntax_Syntax.Tm_constant c, FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5532 = FStar_Const.eq_const c d in
            if uu____5532
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar (uv, uu____5539),
           FStar_Syntax_Syntax.Tm_uvar (uv', uu____5541)) ->
            let uu____5590 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5590
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine (x, uu____5597),
           FStar_Syntax_Syntax.Tm_refine (y, uu____5599)) ->
            let uu____5608 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5608 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x, uu____5610), uu____5611) ->
            let uu____5616 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5616 head_match
        | (uu____5617, FStar_Syntax_Syntax.Tm_refine (x, uu____5619)) ->
            let uu____5624 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5624 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5625,
           FStar_Syntax_Syntax.Tm_type uu____5626) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow uu____5627,
           FStar_Syntax_Syntax.Tm_arrow uu____5628) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_match uu____5653,
           FStar_Syntax_Syntax.Tm_match uu____5654) ->
            ((let uu____5700 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "RelDelta") in
              if uu____5700
              then
                FStar_ST.op_Colon_Equals FStar_Syntax_Util.debug_term_eq true
              else ());
             (let uu____5727 = FStar_Syntax_Util.term_eq t11 t21 in
              if uu____5727
              then FullMatch
              else
                MisMatch
                  (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.None)))
        | (FStar_Syntax_Syntax.Tm_app (head1, uu____5734),
           FStar_Syntax_Syntax.Tm_app (head', uu____5736)) ->
            let uu____5777 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5777 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1, uu____5779), uu____5780) ->
            let uu____5801 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5801 head_match
        | (uu____5802, FStar_Syntax_Syntax.Tm_app (head1, uu____5804)) ->
            let uu____5825 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5825 head_match
        | uu____5826 ->
            let uu____5831 =
              let uu____5840 = delta_depth_of_term env t11 in
              let uu____5843 = delta_depth_of_term env t21 in
              (uu____5840, uu____5843) in
            MisMatch uu____5831
let head_matches_delta :
  'Auu____5855 .
    FStar_TypeChecker_Env.env ->
      'Auu____5855 ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (match_result,
              (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.typ)
                FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
              FStar_Pervasives_Native.tuple2
  =
  fun env ->
    fun wl ->
      fun t1 ->
        fun t2 ->
          let maybe_inline t =
            let uu____5888 = FStar_Syntax_Util.head_and_args t in
            match uu____5888 with
            | (head1, uu____5906) ->
                let uu____5927 =
                  let uu____5928 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5928.FStar_Syntax_Syntax.n in
                (match uu____5927 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5934 =
                       let uu____5935 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5935 FStar_Option.isSome in
                     if uu____5934
                     then
                       let uu____5954 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5954
                         (fun _0_45 -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____5958 -> FStar_Pervasives_Native.None) in
          let success d r t11 t21 =
            (r,
              (if d > (Prims.parse_int "0")
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None)) in
          let fail1 r = (r, FStar_Pervasives_Native.None) in
          let rec aux retry n_delta t11 t21 =
            let r = head_matches env t11 t21 in
            match r with
            | MisMatch
                (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational), uu____6061)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6079 =
                     let uu____6088 = maybe_inline t11 in
                     let uu____6091 = maybe_inline t21 in
                     (uu____6088, uu____6091) in
                   match uu____6079 with
                   | (FStar_Pervasives_Native.None,
                      FStar_Pervasives_Native.None) -> fail1 r
                   | (FStar_Pervasives_Native.Some t12,
                      FStar_Pervasives_Native.None) ->
                       aux false (n_delta + (Prims.parse_int "1")) t12 t21
                   | (FStar_Pervasives_Native.None,
                      FStar_Pervasives_Native.Some t22) ->
                       aux false (n_delta + (Prims.parse_int "1")) t11 t22
                   | (FStar_Pervasives_Native.Some t12,
                      FStar_Pervasives_Native.Some t22) ->
                       aux false (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch
                (uu____6128, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6146 =
                     let uu____6155 = maybe_inline t11 in
                     let uu____6158 = maybe_inline t21 in
                     (uu____6155, uu____6158) in
                   match uu____6146 with
                   | (FStar_Pervasives_Native.None,
                      FStar_Pervasives_Native.None) -> fail1 r
                   | (FStar_Pervasives_Native.Some t12,
                      FStar_Pervasives_Native.None) ->
                       aux false (n_delta + (Prims.parse_int "1")) t12 t21
                   | (FStar_Pervasives_Native.None,
                      FStar_Pervasives_Native.Some t22) ->
                       aux false (n_delta + (Prims.parse_int "1")) t11 t22
                   | (FStar_Pervasives_Native.Some t12,
                      FStar_Pervasives_Native.Some t22) ->
                       aux false (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch
                (FStar_Pervasives_Native.Some d1,
                 FStar_Pervasives_Native.Some d2)
                when d1 = d2 ->
                let uu____6201 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____6201 with
                 | FStar_Pervasives_Native.None -> fail1 r
                 | FStar_Pervasives_Native.Some d ->
                     let t12 =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d;
                         FStar_TypeChecker_Normalize.Weak;
                         FStar_TypeChecker_Normalize.HNF] env wl t11 in
                     let t22 =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d;
                         FStar_TypeChecker_Normalize.Weak;
                         FStar_TypeChecker_Normalize.HNF] env wl t21 in
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch
                (FStar_Pervasives_Native.Some d1,
                 FStar_Pervasives_Native.Some d2)
                ->
                let d1_greater_than_d2 =
                  FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
                let uu____6224 =
                  if d1_greater_than_d2
                  then
                    let t1' =
                      normalize_refinement
                        [FStar_TypeChecker_Normalize.UnfoldUntil d2;
                        FStar_TypeChecker_Normalize.Weak;
                        FStar_TypeChecker_Normalize.HNF] env wl t11 in
                    (t1', t21)
                  else
                    (let t2' =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                         FStar_TypeChecker_Normalize.Weak;
                         FStar_TypeChecker_Normalize.HNF] env wl t21 in
                     (t11, t2')) in
                (match uu____6224 with
                 | (t12, t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6248 -> fail1 r
            | uu____6257 -> success n_delta r t11 t21 in
          let r = aux true (Prims.parse_int "0") t1 t2 in
          (let uu____6270 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta") in
           if uu____6270
           then
             let uu____6271 = FStar_Syntax_Print.term_to_string t1 in
             let uu____6272 = FStar_Syntax_Print.term_to_string t2 in
             let uu____6273 =
               string_of_match_result (FStar_Pervasives_Native.fst r) in
             FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6271
               uu____6272 uu____6273
           else ());
          r
type tc =
  | T of (FStar_Syntax_Syntax.term,
  FStar_Syntax_Syntax.binders ->
    FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C of FStar_Syntax_Syntax.comp [@@deriving show]
let (uu___is_T : tc -> Prims.bool) =
  fun projectee -> match projectee with | T _0 -> true | uu____6313 -> false
let (__proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term,
      FStar_Syntax_Syntax.binders ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | T _0 -> _0
let (uu___is_C : tc -> Prims.bool) =
  fun projectee -> match projectee with | C _0 -> true | uu____6349 -> false
let (__proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp) =
  fun projectee -> match projectee with | C _0 -> _0
type tcs = tc Prims.list[@@deriving show]
let (tc_to_string : tc -> Prims.string) =
  fun uu___107_6361 ->
    match uu___107_6361 with
    | T (t, uu____6363) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
let (generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders ->
    fun r ->
      let uu____6379 = FStar_Syntax_Util.type_u () in
      match uu____6379 with
      | (t, uu____6385) ->
          let uu____6386 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____6386
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders ->
    fun r ->
      let uu____6397 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____6397 FStar_Pervasives_Native.fst
let rec (decompose :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (tc Prims.list -> FStar_Syntax_Syntax.term,
        FStar_Syntax_Syntax.term -> Prims.bool,
        (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option, variance,
          tc) FStar_Pervasives_Native.tuple3 Prims.list)
        FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let matches t' =
        let uu____6461 = head_matches env t1 t' in
        match uu____6461 with
        | MisMatch uu____6462 -> false
        | uu____6471 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1, args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x ->
                   fun y ->
                     match (x, y) with
                     | ((uu____6567, imp), T (t2, uu____6570)) -> (t2, imp)
                     | uu____6589 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6656 ->
                    match uu____6656 with
                    | (t2, uu____6670) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____6713 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6713 with
           | (bs1, c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x, imp)::bs3, (T (t2, uu____6788))::tcs2) ->
                       aux
                         (((let uu___132_6823 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___132_6823.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___132_6823.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([], (C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6841 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___108_6894 =
                 match uu___108_6894 with
                 | [] ->
                     FStar_List.rev
                       ((FStar_Pervasives_Native.None, COVARIANT, (C c1)) ::
                       out)
                 | hd1::rest ->
                     decompose1
                       (((FStar_Pervasives_Native.Some hd1), CONTRAVARIANT,
                          (T
                             (((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____7011 = decompose1 [] bs1 in
               (rebuild, matches, uu____7011))
      | uu____7060 ->
          let rebuild uu___109_7066 =
            match uu___109_7066 with
            | [] -> t1
            | uu____7069 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2 -> FStar_Util.return_all true)), [])
let (un_T : tc -> FStar_Syntax_Syntax.term) =
  fun uu___110_7100 ->
    match uu___110_7100 with
    | T (t, uu____7102) -> t
    | uu____7111 -> failwith "Impossible"
let (arg_of_tc : tc -> FStar_Syntax_Syntax.arg) =
  fun uu___111_7114 ->
    match uu___111_7114 with
    | T (t, uu____7116) -> FStar_Syntax_Syntax.as_arg t
    | uu____7125 -> failwith "Impossible"
let (imitation_sub_probs :
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.args ->
          (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,
            variance, tc) FStar_Pervasives_Native.tuple3 Prims.list ->
            (FStar_TypeChecker_Common.prob Prims.list, tc Prims.list,
              FStar_Syntax_Syntax.formula) FStar_Pervasives_Native.tuple3)
  =
  fun orig ->
    fun env ->
      fun scope ->
        fun ps ->
          fun qs ->
            let r = p_loc orig in
            let rel = p_rel orig in
            let sub_prob scope1 args q =
              match q with
              | (uu____7241, variance, T (ti, mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____7266 = new_uvar r scope1 k in
                  (match uu____7266 with
                   | (gi_xs, gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7284 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____7301 =
                         let uu____7302 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_46 -> FStar_TypeChecker_Common.TProb _0_46)
                           uu____7302 in
                       ((T (gi_xs, mk_kind)), uu____7301))
              | (uu____7315, uu____7316, C uu____7317) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7464 =
                    match q with
                    | (bopt, variance, C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti, uopt);
                         FStar_Syntax_Syntax.pos = uu____7481;
                         FStar_Syntax_Syntax.vars = uu____7482;_})
                        ->
                        let uu____7505 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7505 with
                         | (T (gi_xs, uu____7529), prob) ->
                             let uu____7539 =
                               let uu____7540 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_47 -> C _0_47)
                                 uu____7540 in
                             (uu____7539, [prob])
                         | uu____7543 -> failwith "impossible")
                    | (bopt, variance, C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti, uopt);
                         FStar_Syntax_Syntax.pos = uu____7558;
                         FStar_Syntax_Syntax.vars = uu____7559;_})
                        ->
                        let uu____7582 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7582 with
                         | (T (gi_xs, uu____7606), prob) ->
                             let uu____7616 =
                               let uu____7617 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48 -> C _0_48)
                                 uu____7617 in
                             (uu____7616, [prob])
                         | uu____7620 -> failwith "impossible")
                    | (uu____7631, uu____7632, C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7634;
                         FStar_Syntax_Syntax.vars = uu____7635;_})
                        ->
                        let components =
                          FStar_All.pipe_right
                            c.FStar_Syntax_Syntax.effect_args
                            (FStar_List.map
                               (fun t ->
                                  (FStar_Pervasives_Native.None, INVARIANT,
                                    (T
                                       ((FStar_Pervasives_Native.fst t),
                                         generic_kind))))) in
                        let components1 =
                          (FStar_Pervasives_Native.None, COVARIANT,
                            (T
                               ((c.FStar_Syntax_Syntax.result_typ),
                                 kind_type)))
                          :: components in
                        let uu____7766 =
                          let uu____7775 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7775 FStar_List.unzip in
                        (match uu____7766 with
                         | (tcs, sub_probs) ->
                             let gi_xs =
                               let uu____7829 =
                                 let uu____7830 =
                                   let uu____7833 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7833 un_T in
                                 let uu____7834 =
                                   let uu____7843 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7843
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7830;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7834;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7829 in
                             ((C gi_xs), sub_probs))
                    | uu____7852 ->
                        let uu____7865 = sub_prob scope1 args q in
                        (match uu____7865 with
                         | (ktec, prob) -> (ktec, [prob])) in
                  (match uu____7464 with
                   | (tc, probs) ->
                       let uu____7896 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some (b, imp),
                             uu____7959, uu____7960),
                            T (t, uu____7962)) ->
                             let b1 =
                               ((let uu___133_7999 = b in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___133_7999.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___133_7999.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp) in
                             let uu____8000 =
                               let uu____8007 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1 in
                               uu____8007 :: args in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____8000)
                         | uu____8042 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7896 with
                        | (bopt, scope2, args1) ->
                            let uu____8126 = aux scope2 args1 qs2 in
                            (match uu____8126 with
                             | (sub_probs, tcs, f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None ->
                                       let f1 =
                                         let uu____8164 =
                                           let uu____8167 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst)) in
                                           f :: uu____8167 in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8164 in
                                       (def_check_closed (p_loc orig)
                                          "imitation_sub_probs (1)" f1;
                                        f1)
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let f1 =
                                         let uu____8192 =
                                           let uu____8195 =
                                             FStar_Syntax_Util.mk_forall u_b
                                               (FStar_Pervasives_Native.fst b)
                                               f in
                                           let uu____8196 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst)) in
                                           uu____8195 :: uu____8196 in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8192 in
                                       (def_check_closed (p_loc orig)
                                          "imitation_sub_probs (2)" f1;
                                        f1) in
                                 ((FStar_List.append probs sub_probs), (tc ::
                                   tcs), f1)))) in
            aux scope ps qs
type flex_t =
  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.uvar,
    FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple4[@@deriving show]
type im_or_proj_t =
  (((FStar_Syntax_Syntax.uvar, FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,
     FStar_Syntax_Syntax.binders, FStar_Syntax_Syntax.comp)
     FStar_Pervasives_Native.tuple3,
    FStar_Syntax_Syntax.arg Prims.list,
    (tc Prims.list -> FStar_Syntax_Syntax.typ,
      FStar_Syntax_Syntax.typ -> Prims.bool,
      (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option, variance,
        tc) FStar_Pervasives_Native.tuple3 Prims.list)
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
  'Auu____8265 .
    worklist ->
      (FStar_Syntax_Syntax.term, 'Auu____8265)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term, 'Auu____8265)
          FStar_TypeChecker_Common.problem
  =
  fun wl ->
    fun p ->
      let uu___134_8286 = p in
      let uu____8291 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____8292 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___134_8286.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8291;
        FStar_TypeChecker_Common.relation =
          (uu___134_8286.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8292;
        FStar_TypeChecker_Common.element =
          (uu___134_8286.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___134_8286.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___134_8286.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___134_8286.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___134_8286.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___134_8286.FStar_TypeChecker_Common.rank)
      }
let (compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun wl ->
    fun p ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8304 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____8304
            (fun _0_49 -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____8313 -> p
let (rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int, FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun wl ->
    fun pr ->
      let prob =
        let uu____8333 = compress_prob wl pr in
        FStar_All.pipe_right uu____8333 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8343 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8343 with
           | (lh, uu____8363) ->
               let uu____8384 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8384 with
                | (rh, uu____8404) ->
                    let uu____8425 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8442,
                         FStar_Syntax_Syntax.Tm_uvar uu____8443) ->
                          (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8480, uu____8481)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8502, FStar_Syntax_Syntax.Tm_uvar uu____8503)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8524, uu____8525)
                          ->
                          let uu____8542 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____8542 with
                           | (b, ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None ->
                                    (flex_rigid, tp)
                                | uu____8591 ->
                                    let rank =
                                      let uu____8599 = is_top_level_prob prob in
                                      if uu____8599
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8601 =
                                      let uu___135_8606 = tp in
                                      let uu____8611 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___135_8606.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___135_8606.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___135_8606.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8611;
                                        FStar_TypeChecker_Common.element =
                                          (uu___135_8606.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___135_8606.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___135_8606.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___135_8606.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___135_8606.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___135_8606.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8601)))
                      | (uu____8622, FStar_Syntax_Syntax.Tm_uvar uu____8623)
                          ->
                          let uu____8640 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8640 with
                           | (b, ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None ->
                                    (rigid_flex, tp)
                                | uu____8689 ->
                                    let uu____8696 =
                                      let uu___136_8703 = tp in
                                      let uu____8708 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___136_8703.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8708;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___136_8703.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___136_8703.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___136_8703.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___136_8703.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___136_8703.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___136_8703.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___136_8703.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___136_8703.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8696)))
                      | (uu____8725, uu____8726) -> (rigid_rigid, tp) in
                    (match uu____8425 with
                     | (rank, tp1) ->
                         let uu____8745 =
                           FStar_All.pipe_right
                             (let uu___137_8751 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___137_8751.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___137_8751.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___137_8751.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___137_8751.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___137_8751.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___137_8751.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___137_8751.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___137_8751.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___137_8751.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50 ->
                                FStar_TypeChecker_Common.TProb _0_50) in
                         (rank, uu____8745))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8761 =
            FStar_All.pipe_right
              (let uu___138_8767 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___138_8767.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___138_8767.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___138_8767.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___138_8767.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___138_8767.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___138_8767.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___138_8767.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___138_8767.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___138_8767.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51 -> FStar_TypeChecker_Common.CProb _0_51) in
          (rigid_rigid, uu____8761)
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,
      FStar_TypeChecker_Common.prob Prims.list, Prims.int)
      FStar_Pervasives_Native.tuple3)
  =
  fun wl ->
    let rec aux uu____8822 probs =
      match uu____8822 with
      | (min_rank, min1, out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8875 = rank wl hd1 in
               (match uu____8875 with
                | (rank1, hd2) ->
                    if rank1 <= flex_rigid_eq
                    then
                      (match min1 with
                       | FStar_Pervasives_Native.None ->
                           ((FStar_Pervasives_Native.Some hd2),
                             (FStar_List.append out tl1), rank1)
                       | FStar_Pervasives_Native.Some m ->
                           ((FStar_Pervasives_Native.Some hd2),
                             (FStar_List.append out (m :: tl1)), rank1))
                    else
                      if rank1 < min_rank
                      then
                        (match min1 with
                         | FStar_Pervasives_Native.None ->
                             aux
                               (rank1, (FStar_Pervasives_Native.Some hd2),
                                 out) tl1
                         | FStar_Pervasives_Native.Some m ->
                             aux
                               (rank1, (FStar_Pervasives_Native.Some hd2), (m
                                 :: out)) tl1)
                      else aux (min_rank, min1, (hd2 :: out)) tl1)) in
    aux
      ((flex_flex + (Prims.parse_int "1")), FStar_Pervasives_Native.None, [])
      wl.attempting
let (is_flex_rigid : Prims.int -> Prims.bool) =
  fun rank1 -> (flex_refine_inner <= rank1) && (rank1 <= flex_rigid)
let (is_rigid_flex : Prims.int -> Prims.bool) =
  fun rank1 -> (rigid_flex <= rank1) && (rank1 <= refine_flex)
type univ_eq_sol =
  | UDeferred of worklist 
  | USolved of worklist 
  | UFailed of Prims.string [@@deriving show]
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | UDeferred _0 -> true | uu____8982 -> false
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | UDeferred _0 -> _0
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | USolved _0 -> true | uu____8994 -> false
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | USolved _0 -> _0
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | UFailed _0 -> true | uu____9006 -> false
let (__proj__UFailed__item___0 : univ_eq_sol -> Prims.string) =
  fun projectee -> match projectee with | UFailed _0 -> _0
let rec (really_solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun pid_orig ->
    fun wl ->
      fun u1 ->
        fun u2 ->
          let u11 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1 in
          let u21 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2 in
          let rec occurs_univ v1 u =
            match u with
            | FStar_Syntax_Syntax.U_max us ->
                FStar_All.pipe_right us
                  (FStar_Util.for_some
                     (fun u3 ->
                        let uu____9046 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____9046 with
                        | (k, uu____9052) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9062 -> false)))
            | uu____9063 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs ->
                      fun uv1 ->
                        let uu____9111 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2 ->
                                  let uu____9117 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2 in
                                  uu____9117 = (Prims.parse_int "0"))) in
                        if uu____9111 then uv1 :: uvs else uvs) []) in
            let filter1 =
              FStar_List.filter
                (fun u ->
                   let uu____9131 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u' ->
                             let uu____9137 =
                               FStar_Syntax_Util.compare_univs u u' in
                             uu____9137 = (Prims.parse_int "0"))) in
                   Prims.op_Negation uu____9131) in
            let uu____9138 = filter1 u12 in
            let uu____9141 = filter1 u22 in (uu____9138, uu____9141) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1, FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____9164 = filter_out_common_univs us1 us2 in
                (match uu____9164 with
                 | (us11, us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13, u23::us23) ->
                             let uu____9217 =
                               really_solve_universe_eq pid_orig wl1 u13 u23 in
                             (match uu____9217 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____9220 -> USolved wl1 in
                       aux wl us11 us21
                     else
                       (let uu____9230 =
                          let uu____9231 =
                            FStar_Syntax_Print.univ_to_string u12 in
                          let uu____9232 =
                            FStar_Syntax_Print.univ_to_string u22 in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____9231
                            uu____9232 in
                        UFailed uu____9230))
            | (FStar_Syntax_Syntax.U_max us, u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9252 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____9252 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u', FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9274 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____9274 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____9277 ->
                let uu____9282 =
                  let uu____9283 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____9284 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9283
                    uu____9284 msg in
                UFailed uu____9282 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9285, uu____9286) ->
              let uu____9287 =
                let uu____9288 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9289 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9288 uu____9289 in
              failwith uu____9287
          | (FStar_Syntax_Syntax.U_unknown, uu____9290) ->
              let uu____9291 =
                let uu____9292 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9293 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9292 uu____9293 in
              failwith uu____9291
          | (uu____9294, FStar_Syntax_Syntax.U_bvar uu____9295) ->
              let uu____9296 =
                let uu____9297 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9298 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9297 uu____9298 in
              failwith uu____9296
          | (uu____9299, FStar_Syntax_Syntax.U_unknown) ->
              let uu____9300 =
                let uu____9301 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9302 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9301 uu____9302 in
              failwith uu____9300
          | (FStar_Syntax_Syntax.U_name x, FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12, FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1, FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9326 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____9326
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1, u) ->
              let u3 = norm_univ wl u in
              let uu____9348 = occurs_univ v1 u3 in
              if uu____9348
              then
                let uu____9349 =
                  let uu____9350 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9351 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9350 uu____9351 in
                try_umax_components u11 u21 uu____9349
              else
                (let uu____9353 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9353)
          | (u, FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9373 = occurs_univ v1 u3 in
              if uu____9373
              then
                let uu____9374 =
                  let uu____9375 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9376 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9375 uu____9376 in
                try_umax_components u11 u21 uu____9374
              else
                (let uu____9378 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9378)
          | (FStar_Syntax_Syntax.U_max uu____9387, uu____9388) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9394 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9394
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9396, FStar_Syntax_Syntax.U_max uu____9397) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9403 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9403
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9405,
             FStar_Syntax_Syntax.U_zero) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9406,
             FStar_Syntax_Syntax.U_name uu____9407) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ
             uu____9408) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name
             uu____9409) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9410,
             FStar_Syntax_Syntax.U_succ uu____9411) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9412,
             FStar_Syntax_Syntax.U_zero) -> UFailed "Incompatible universes"
let (solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun orig ->
    fun wl ->
      fun u1 ->
        fun u2 ->
          if (wl.tcenv).FStar_TypeChecker_Env.lax_universes
          then USolved wl
          else really_solve_universe_eq orig wl u1 u2
let match_num_binders :
  'a 'b .
    ('a Prims.list, 'a Prims.list -> 'b) FStar_Pervasives_Native.tuple2 ->
      ('a Prims.list, 'a Prims.list -> 'b) FStar_Pervasives_Native.tuple2 ->
        (('a Prims.list, 'b) FStar_Pervasives_Native.tuple2,
          ('a Prims.list, 'b) FStar_Pervasives_Native.tuple2)
          FStar_Pervasives_Native.tuple2
  =
  fun bc1 ->
    fun bc2 ->
      let uu____9498 = bc1 in
      match uu____9498 with
      | (bs1, mk_cod1) ->
          let uu____9539 = bc2 in
          (match uu____9539 with
           | (bs2, mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs, y::ys) ->
                     let uu____9643 = aux xs ys in
                     (match uu____9643 with
                      | ((xs1, xr), (ys1, yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs, ys) ->
                     let uu____9726 =
                       let uu____9733 = mk_cod1 xs in ([], uu____9733) in
                     let uu____9736 =
                       let uu____9743 = mk_cod2 ys in ([], uu____9743) in
                     (uu____9726, uu____9736) in
               aux bs1 bs2)
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env ->
    fun probs ->
      (let uu____9854 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9854
       then
         let uu____9855 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9855
       else ());
      (let uu____9857 = next_prob probs in
       match uu____9857 with
       | (FStar_Pervasives_Native.Some hd1, tl1, rank1) ->
           let probs1 =
             let uu___139_9878 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___139_9878.wl_deferred);
               ctr = (uu___139_9878.ctr);
               defer_ok = (uu___139_9878.defer_ok);
               smt_ok = (uu___139_9878.smt_ok);
               tcenv = (uu___139_9878.tcenv)
             } in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                if
                  ((Prims.op_Negation probs1.defer_ok) &&
                     (flex_refine_inner <= rank1))
                    && (rank1 <= flex_rigid)
                then
                  let uu____9889 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9889 with
                   | FStar_Pervasives_Native.None ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9894 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9894 with
                     | FStar_Pervasives_Native.None ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None, uu____9899, uu____9900) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9917 ->
                let uu____9926 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9985 ->
                          match uu____9985 with
                          | (c, uu____9993, uu____9994) -> c < probs.ctr)) in
                (match uu____9926 with
                 | (attempt1, rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10035 =
                            FStar_List.map
                              (fun uu____10050 ->
                                 match uu____10050 with
                                 | (uu____10061, x, y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____10035
                      | uu____10064 ->
                          let uu____10073 =
                            let uu___140_10074 = probs in
                            let uu____10075 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10096 ->
                                      match uu____10096 with
                                      | (uu____10103, uu____10104, y) -> y)) in
                            {
                              attempting = uu____10075;
                              wl_deferred = rest;
                              ctr = (uu___140_10074.ctr);
                              defer_ok = (uu___140_10074.defer_ok);
                              smt_ok = (uu___140_10074.smt_ok);
                              tcenv = (uu___140_10074.tcenv)
                            } in
                          solve env uu____10073))))
and (solve_one_universe_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> worklist -> solution)
  =
  fun env ->
    fun orig ->
      fun u1 ->
        fun u2 ->
          fun wl ->
            let uu____10111 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____10111 with
            | USolved wl1 ->
                let uu____10113 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____10113
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 -> solve env (defer "" orig wl1)
and (solve_maybe_uinsts :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> worklist -> univ_eq_sol)
  =
  fun env ->
    fun orig ->
      fun t1 ->
        fun t2 ->
          fun wl ->
            let rec aux wl1 us1 us2 =
              match (us1, us2) with
              | ([], []) -> USolved wl1
              | (u1::us11, u2::us21) ->
                  let uu____10159 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____10159 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10162 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10174;
                  FStar_Syntax_Syntax.vars = uu____10175;_},
                us1),
               FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10178;
                  FStar_Syntax_Syntax.vars = uu____10179;_},
                us2)) ->
                let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10199, uu____10200) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10207, FStar_Syntax_Syntax.Tm_uinst uu____10208) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10215 -> USolved wl
and (giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> Prims.string -> solution)
  =
  fun env ->
    fun orig ->
      fun wl ->
        fun msg ->
          if wl.defer_ok
          then
            ((let uu____10225 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____10225
              then
                let uu____10226 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10226 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and (solve_rigid_flex_meet :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env ->
    fun tp ->
      fun wl ->
        (let uu____10235 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10235
         then
           let uu____10236 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____10236
         else ());
        (let uu____10238 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____10238 with
         | (u, args) ->
             let rec disjoin t1 t2 =
               let uu____10300 = head_matches_delta env () t1 t2 in
               match uu____10300 with
               | (mr, ts) ->
                   (match mr with
                    | MisMatch uu____10341 -> FStar_Pervasives_Native.None
                    | FullMatch ->
                        (match ts with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11, t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch ->
                        let uu____10390 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11, t21) ->
                              let uu____10405 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____10406 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____10405, uu____10406)
                          | FStar_Pervasives_Native.None ->
                              let uu____10411 =
                                FStar_Syntax_Subst.compress t1 in
                              let uu____10412 =
                                FStar_Syntax_Subst.compress t2 in
                              (uu____10411, uu____10412) in
                        (match uu____10390 with
                         | (t11, t21) ->
                             let eq_prob t12 t22 =
                               let uu____10438 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_52 ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____10438 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine (x, phi1),
                                 FStar_Syntax_Syntax.Tm_refine (y, phi2)) ->
                                  let uu____10469 =
                                    let uu____10478 =
                                      let uu____10481 =
                                        let uu____10484 =
                                          let uu____10485 =
                                            let uu____10492 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____10492) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10485 in
                                        FStar_Syntax_Syntax.mk uu____10484 in
                                      uu____10481
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____10500 =
                                      let uu____10503 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____10503] in
                                    (uu____10478, uu____10500) in
                                  FStar_Pervasives_Native.Some uu____10469
                              | (uu____10516, FStar_Syntax_Syntax.Tm_refine
                                 (x, uu____10518)) ->
                                  let uu____10523 =
                                    let uu____10530 =
                                      let uu____10533 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____10533] in
                                    (t11, uu____10530) in
                                  FStar_Pervasives_Native.Some uu____10523
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x, uu____10543), uu____10544) ->
                                  let uu____10549 =
                                    let uu____10556 =
                                      let uu____10559 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____10559] in
                                    (t21, uu____10556) in
                                  FStar_Pervasives_Native.Some uu____10549
                              | uu____10568 ->
                                  let uu____10573 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____10573 with
                                   | (head1, uu____10597) ->
                                       let uu____10618 =
                                         let uu____10619 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____10619.FStar_Syntax_Syntax.n in
                                       (match uu____10618 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10630;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10632;_}
                                            ->
                                            let prev =
                                              if i > (Prims.parse_int "1")
                                              then
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                  (i - (Prims.parse_int "1"))
                                              else
                                                FStar_Syntax_Syntax.Delta_constant in
                                            let t12 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.Weak;
                                                FStar_TypeChecker_Normalize.HNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t11 in
                                            let t22 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.Weak;
                                                FStar_TypeChecker_Normalize.HNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t21 in
                                            disjoin t12 t22
                                        | uu____10639 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv, uu____10652) ->
                  let uu____10677 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___112_10703 ->
                            match uu___112_10703 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10710 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10710 with
                                      | (u', uu____10726) ->
                                          let uu____10747 =
                                            let uu____10748 = whnf env u' in
                                            uu____10748.FStar_Syntax_Syntax.n in
                                          (match uu____10747 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv', uu____10752) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10777 -> false))
                                 | uu____10778 -> false)
                            | uu____10781 -> false)) in
                  (match uu____10677 with
                   | (lower_bounds, rest) ->
                       let rec make_lower_bound uu____10815 tps =
                         match uu____10815 with
                         | (bound, sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10863 =
                                    let uu____10872 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10872 in
                                  (match uu____10863 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1, sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None)
                              | uu____10907 -> FStar_Pervasives_Native.None) in
                       let uu____10916 =
                         let uu____10925 =
                           let uu____10932 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10932, []) in
                         make_lower_bound uu____10925 lower_bounds in
                       (match uu____10916 with
                        | FStar_Pervasives_Native.None ->
                            ((let uu____10944 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10944
                              then
                                FStar_Util.print_string "No lower bounds\n"
                              else ());
                             FStar_Pervasives_Native.None)
                        | FStar_Pervasives_Native.Some (lhs_bound, sub_probs)
                            ->
                            let eq_prob =
                              new_problem env lhs_bound
                                FStar_TypeChecker_Common.EQ
                                tp.FStar_TypeChecker_Common.rhs
                                FStar_Pervasives_Native.None
                                tp.FStar_TypeChecker_Common.loc
                                "meeting refinements" in
                            ((let uu____10964 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10964
                              then
                                let wl' =
                                  let uu___141_10966 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___141_10966.wl_deferred);
                                    ctr = (uu___141_10966.ctr);
                                    defer_ok = (uu___141_10966.defer_ok);
                                    smt_ok = (uu___141_10966.smt_ok);
                                    tcenv = (uu___141_10966.tcenv)
                                  } in
                                let uu____10967 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10967
                              else ());
                             (let uu____10969 =
                                solve_t env eq_prob
                                  (let uu___142_10971 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___142_10971.wl_deferred);
                                     ctr = (uu___142_10971.ctr);
                                     defer_ok = (uu___142_10971.defer_ok);
                                     smt_ok = (uu___142_10971.smt_ok);
                                     tcenv = (uu___142_10971.tcenv)
                                   }) in
                              match uu____10969 with
                              | Success uu____10974 ->
                                  let wl1 =
                                    let uu___143_10976 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___143_10976.wl_deferred);
                                      ctr = (uu___143_10976.ctr);
                                      defer_ok = (uu___143_10976.defer_ok);
                                      smt_ok = (uu___143_10976.smt_ok);
                                      tcenv = (uu___143_10976.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10978 =
                                    FStar_List.fold_left
                                      (fun wl3 ->
                                         fun p ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10983 -> FStar_Pervasives_Native.None))))
              | uu____10984 -> failwith "Impossible: Not a rigid-flex"))
and (solve_flex_rigid_join :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env ->
    fun tp ->
      fun wl ->
        (let uu____10993 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10993
         then
           let uu____10994 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10994
         else ());
        (let uu____10996 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10996 with
         | (u, args) ->
             let uu____11035 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____11035 with
              | (ok, head_match1, partial_match, fallback, failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____11076 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____11076 with
                    | (h1, args1) ->
                        let uu____11117 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____11117 with
                         | (h2, uu____11137) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar tc1,
                                 FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____11164 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____11164
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____11182 =
                                          let uu____11185 =
                                            let uu____11186 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_53 ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____11186 in
                                          [uu____11185] in
                                        FStar_Pervasives_Native.Some
                                          uu____11182))
                                  else FStar_Pervasives_Native.None
                              | (FStar_Syntax_Syntax.Tm_name a,
                                 FStar_Syntax_Syntax.Tm_name b) ->
                                  if FStar_Syntax_Syntax.bv_eq a b
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____11219 =
                                          let uu____11222 =
                                            let uu____11223 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54 ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____11223 in
                                          [uu____11222] in
                                        FStar_Pervasives_Native.Some
                                          uu____11219))
                                  else FStar_Pervasives_Native.None
                              | uu____11237 -> FStar_Pervasives_Native.None)) in
                  let conjoin t1 t2 =
                    match ((t1.FStar_Syntax_Syntax.n),
                            (t2.FStar_Syntax_Syntax.n))
                    with
                    | (FStar_Syntax_Syntax.Tm_refine (x, phi1),
                       FStar_Syntax_Syntax.Tm_refine (y, phi2)) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort
                            y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             let x1 = FStar_Syntax_Syntax.freshen_bv x in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x1)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let uu____11327 =
                               let uu____11336 =
                                 let uu____11339 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____11339 in
                               (uu____11336, m1) in
                             FStar_Pervasives_Native.Some uu____11327)
                    | (uu____11352, FStar_Syntax_Syntax.Tm_refine
                       (y, uu____11354)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine (x, uu____11402),
                       uu____11403) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11450 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv, uu____11503) ->
                       let uu____11528 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___113_11554 ->
                                 match uu___113_11554 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11561 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____11561 with
                                           | (u', uu____11577) ->
                                               let uu____11598 =
                                                 let uu____11599 =
                                                   whnf env u' in
                                                 uu____11599.FStar_Syntax_Syntax.n in
                                               (match uu____11598 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv', uu____11603) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11628 -> false))
                                      | uu____11629 -> false)
                                 | uu____11632 -> false)) in
                       (match uu____11528 with
                        | (upper_bounds, rest) ->
                            let rec make_upper_bound uu____11670 tps =
                              match uu____11670 with
                              | (bound, sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11732 =
                                         let uu____11743 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11743 in
                                       (match uu____11732 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1, sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11794 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11805 =
                              let uu____11816 =
                                let uu____11825 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11825, []) in
                              make_upper_bound uu____11816 upper_bounds in
                            (match uu____11805 with
                             | FStar_Pervasives_Native.None ->
                                 ((let uu____11839 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11839
                                   then
                                     FStar_Util.print_string
                                       "No upper bounds\n"
                                   else ());
                                  FStar_Pervasives_Native.None)
                             | FStar_Pervasives_Native.Some
                                 (rhs_bound, sub_probs) ->
                                 let eq_prob =
                                   new_problem env
                                     tp.FStar_TypeChecker_Common.lhs
                                     FStar_TypeChecker_Common.EQ rhs_bound
                                     FStar_Pervasives_Native.None
                                     tp.FStar_TypeChecker_Common.loc
                                     "joining refinements" in
                                 ((let uu____11865 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11865
                                   then
                                     let wl' =
                                       let uu___144_11867 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___144_11867.wl_deferred);
                                         ctr = (uu___144_11867.ctr);
                                         defer_ok = (uu___144_11867.defer_ok);
                                         smt_ok = (uu___144_11867.smt_ok);
                                         tcenv = (uu___144_11867.tcenv)
                                       } in
                                     let uu____11868 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11868
                                   else ());
                                  (let uu____11870 =
                                     solve_t env eq_prob
                                       (let uu___145_11872 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___145_11872.wl_deferred);
                                          ctr = (uu___145_11872.ctr);
                                          defer_ok =
                                            (uu___145_11872.defer_ok);
                                          smt_ok = (uu___145_11872.smt_ok);
                                          tcenv = (uu___145_11872.tcenv)
                                        }) in
                                   match uu____11870 with
                                   | Success uu____11875 ->
                                       let wl1 =
                                         let uu___146_11877 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___146_11877.wl_deferred);
                                           ctr = (uu___146_11877.ctr);
                                           defer_ok =
                                             (uu___146_11877.defer_ok);
                                           smt_ok = (uu___146_11877.smt_ok);
                                           tcenv = (uu___146_11877.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11879 =
                                         FStar_List.fold_left
                                           (fun wl3 ->
                                              fun p ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11884 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11885 -> failwith "Impossible: Not a flex-rigid")))
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
  fun env ->
    fun bs1 ->
      fun bs2 ->
        fun orig ->
          fun wl ->
            fun rhs ->
              let rec aux scope env1 subst1 xs ys =
                match (xs, ys) with
                | ([], []) ->
                    let rhs_prob = rhs scope env1 subst1 in
                    ((let uu____11960 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11960
                      then
                        let uu____11961 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11961
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1, imp)::xs1, (hd2, imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___147_12015 = hd1 in
                      let uu____12016 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___147_12015.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___147_12015.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____12016
                      } in
                    let hd21 =
                      let uu___148_12020 = hd2 in
                      let uu____12021 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___148_12020.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___148_12020.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____12021
                      } in
                    let prob =
                      let uu____12025 =
                        let uu____12030 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____12030 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_55 -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____12025 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____12041 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____12041 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____12045 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1 in
                    (match uu____12045 with
                     | FStar_Util.Inl (sub_probs, phi) ->
                         let phi1 =
                           let uu____12083 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____12088 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____12083 uu____12088 in
                         ((let uu____12098 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____12098
                           then
                             let uu____12099 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____12100 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____12099 uu____12100
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail1 -> fail1)
                | uu____12123 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____12133 = aux scope env [] bs1 bs2 in
              match uu____12133 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs, phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____12158 = compress_tprob wl problem in
         solve_t' env uu____12158 wl)
and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____12192 = head_matches_delta env1 wl1 t1 t2 in
           match uu____12192 with
           | (m, o) ->
               (match (m, o) with
                | (MisMatch uu____12223, uu____12224) ->
                    let rec may_relate head3 =
                      let uu____12249 =
                        let uu____12250 = FStar_Syntax_Subst.compress head3 in
                        uu____12250.FStar_Syntax_Syntax.n in
                      match uu____12249 with
                      | FStar_Syntax_Syntax.Tm_name uu____12253 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____12254 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____12277;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational;
                            FStar_Syntax_Syntax.fv_qual = uu____12278;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____12281;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____12282;
                            FStar_Syntax_Syntax.fv_qual = uu____12283;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t, uu____12287, uu____12288) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t, uu____12330) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t, uu____12336) ->
                          may_relate t
                      | uu____12341 -> false in
                    let uu____12342 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok in
                    if uu____12342
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
                             | FStar_Pervasives_Native.None ->
                                 let x =
                                   FStar_Syntax_Syntax.new_bv
                                     FStar_Pervasives_Native.None t11 in
                                 let u_x =
                                   env1.FStar_TypeChecker_Env.universe_of
                                     env1 t11 in
                                 let uu____12359 =
                                   let uu____12360 =
                                     FStar_Syntax_Syntax.bv_to_name x in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____12360 t21 in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____12359 in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then has_type_guard t1 t2
                           else has_type_guard t2 t1) in
                      let uu____12362 =
                        solve_prob orig (FStar_Pervasives_Native.Some guard)
                          [] wl1 in
                      solve env1 uu____12362
                    else
                      (let uu____12364 =
                         let uu____12365 =
                           FStar_Syntax_Print.term_to_string head1 in
                         let uu____12366 =
                           FStar_Syntax_Print.term_to_string head2 in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____12365 uu____12366 in
                       giveup env1 uu____12364 orig)
                | (uu____12367, FStar_Pervasives_Native.Some (t11, t21)) ->
                    solve_t env1
                      (let uu___149_12381 = problem in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___149_12381.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___149_12381.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___149_12381.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___149_12381.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___149_12381.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___149_12381.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___149_12381.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___149_12381.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____12382, FStar_Pervasives_Native.None) ->
                    ((let uu____12394 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____12394
                      then
                        let uu____12395 =
                          FStar_Syntax_Print.term_to_string t1 in
                        let uu____12396 = FStar_Syntax_Print.tag_of_term t1 in
                        let uu____12397 =
                          FStar_Syntax_Print.term_to_string t2 in
                        let uu____12398 = FStar_Syntax_Print.tag_of_term t2 in
                        FStar_Util.print4
                          "Head matches: %s (%s) and %s (%s)\n" uu____12395
                          uu____12396 uu____12397 uu____12398
                      else ());
                     (let uu____12400 = FStar_Syntax_Util.head_and_args t1 in
                      match uu____12400 with
                      | (head11, args1) ->
                          let uu____12437 =
                            FStar_Syntax_Util.head_and_args t2 in
                          (match uu____12437 with
                           | (head21, args2) ->
                               let nargs = FStar_List.length args1 in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____12491 =
                                   let uu____12492 =
                                     FStar_Syntax_Print.term_to_string head11 in
                                   let uu____12493 = args_to_string args1 in
                                   let uu____12494 =
                                     FStar_Syntax_Print.term_to_string head21 in
                                   let uu____12495 = args_to_string args2 in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____12492 uu____12493 uu____12494
                                     uu____12495 in
                                 giveup env1 uu____12491 orig
                               else
                                 (let uu____12497 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____12503 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2 in
                                       uu____12503 = FStar_Syntax_Util.Equal) in
                                  if uu____12497
                                  then
                                    let uu____12504 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1 in
                                    match uu____12504 with
                                    | USolved wl2 ->
                                        let uu____12506 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2 in
                                        solve env1 uu____12506
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____12510 =
                                       base_and_refinement env1 t1 in
                                     match uu____12510 with
                                     | (base1, refinement1) ->
                                         let uu____12535 =
                                           base_and_refinement env1 t2 in
                                         (match uu____12535 with
                                          | (base2, refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None,
                                                  FStar_Pervasives_Native.None)
                                                   ->
                                                   let uu____12592 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1 in
                                                   (match uu____12592 with
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
                                                            (fun uu____12614
                                                               ->
                                                               fun
                                                                 uu____12615
                                                                 ->
                                                                 match 
                                                                   (uu____12614,
                                                                    uu____12615)
                                                                 with
                                                                 | ((a,
                                                                    uu____12633),
                                                                    (a',
                                                                    uu____12635))
                                                                    ->
                                                                    let uu____12644
                                                                    =
                                                                    let uu____12649
                                                                    =
                                                                    p_scope
                                                                    orig in
                                                                    mk_problem
                                                                    uu____12649
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index" in
                                                                    FStar_All.pipe_left
                                                                    (fun
                                                                    _0_56 ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_56)
                                                                    uu____12644)
                                                            args1 args2 in
                                                        let formula =
                                                          let uu____12655 =
                                                            FStar_List.map
                                                              (fun p ->
                                                                 FStar_Pervasives_Native.fst
                                                                   (p_guard p))
                                                              subprobs in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____12655 in
                                                        let wl3 =
                                                          solve_prob orig
                                                            (FStar_Pervasives_Native.Some
                                                               formula) []
                                                            wl2 in
                                                        solve env1
                                                          (attempt subprobs
                                                             wl3))
                                               | uu____12661 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1) in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2) in
                                                   solve_t env1
                                                     (let uu___150_12697 =
                                                        problem in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___150_12697.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___150_12697.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___150_12697.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___150_12697.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.scope
                                                          =
                                                          (uu___150_12697.FStar_TypeChecker_Common.scope);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___150_12697.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___150_12697.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___150_12697.FStar_TypeChecker_Common.rank)
                                                      }) wl1)))))))) in
         let force_quasi_pattern xs_opt uu____12730 =
           match uu____12730 with
           | (t, u, k, args) ->
               let debug1 f =
                 let uu____12772 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel") in
                 if uu____12772 then f () else () in
               let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                 seen_formals formals res_t args1 =
                 debug1
                   (fun uu____12868 ->
                      let uu____12869 =
                        FStar_Syntax_Print.binders_to_string ", " pat_args in
                      FStar_Util.print1 "pat_args so far: {%s}\n" uu____12869);
                 (match (formals, args1) with
                  | ([], []) ->
                      let pat_args1 =
                        FStar_All.pipe_right (FStar_List.rev pat_args)
                          (FStar_List.map
                             (fun uu____12937 ->
                                match uu____12937 with
                                | (x, imp) ->
                                    let uu____12948 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    (uu____12948, imp))) in
                      let pattern_vars1 = FStar_List.rev pattern_vars in
                      let kk =
                        let uu____12961 = FStar_Syntax_Util.type_u () in
                        match uu____12961 with
                        | (t1, uu____12967) ->
                            let uu____12968 =
                              new_uvar t1.FStar_Syntax_Syntax.pos
                                pattern_vars1 t1 in
                            FStar_Pervasives_Native.fst uu____12968 in
                      let uu____12973 =
                        new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk in
                      (match uu____12973 with
                       | (t', tm_u1) ->
                           let uu____12986 = destruct_flex_t t' in
                           (match uu____12986 with
                            | (uu____13023, u1, k1, uu____13026) ->
                                let all_formals = FStar_List.rev seen_formals in
                                let k2 =
                                  let uu____13085 =
                                    FStar_Syntax_Syntax.mk_Total res_t in
                                  FStar_Syntax_Util.arrow all_formals
                                    uu____13085 in
                                let sol =
                                  let uu____13089 =
                                    let uu____13098 = u_abs k2 all_formals t' in
                                    ((u, k2), uu____13098) in
                                  TERM uu____13089 in
                                let t_app =
                                  FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                    pat_args1 FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos in
                                FStar_Pervasives_Native.Some
                                  (sol, (t_app, u1, k1, pat_args1))))
                  | (formal::formals1, hd1::tl1) ->
                      (debug1
                         (fun uu____13233 ->
                            let uu____13234 =
                              FStar_Syntax_Print.binder_to_string formal in
                            let uu____13235 =
                              FStar_Syntax_Print.args_to_string [hd1] in
                            FStar_Util.print2
                              "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                              uu____13234 uu____13235);
                       (let uu____13248 = pat_var_opt env pat_args hd1 in
                        match uu____13248 with
                        | FStar_Pervasives_Native.None ->
                            (debug1
                               (fun uu____13268 ->
                                  FStar_Util.print_string
                                    "not a pattern var\n");
                             aux pat_args pat_args_set pattern_vars
                               pattern_var_set (formal :: seen_formals)
                               formals1 res_t tl1)
                        | FStar_Pervasives_Native.Some y ->
                            let maybe_pat =
                              match xs_opt with
                              | FStar_Pervasives_Native.None -> true
                              | FStar_Pervasives_Native.Some xs ->
                                  FStar_All.pipe_right xs
                                    (FStar_Util.for_some
                                       (fun uu____13311 ->
                                          match uu____13311 with
                                          | (x, uu____13317) ->
                                              FStar_Syntax_Syntax.bv_eq x
                                                (FStar_Pervasives_Native.fst
                                                   y))) in
                            if Prims.op_Negation maybe_pat
                            then
                              aux pat_args pat_args_set pattern_vars
                                pattern_var_set (formal :: seen_formals)
                                formals1 res_t tl1
                            else
                              (debug1
                                 (fun uu____13332 ->
                                    let uu____13333 =
                                      FStar_Syntax_Print.args_to_string [hd1] in
                                    let uu____13346 =
                                      FStar_Syntax_Print.binder_to_string y in
                                    FStar_Util.print2
                                      "%s (var = %s) maybe pat\n" uu____13333
                                      uu____13346);
                               (let fvs =
                                  FStar_Syntax_Free.names
                                    (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort in
                                let uu____13350 =
                                  let uu____13351 =
                                    FStar_Util.set_is_subset_of fvs
                                      pat_args_set in
                                  Prims.op_Negation uu____13351 in
                                if uu____13350
                                then
                                  (debug1
                                     (fun uu____13363 ->
                                        let uu____13364 =
                                          let uu____13367 =
                                            FStar_Syntax_Print.args_to_string
                                              [hd1] in
                                          let uu____13380 =
                                            let uu____13383 =
                                              FStar_Syntax_Print.binder_to_string
                                                y in
                                            let uu____13384 =
                                              let uu____13387 =
                                                FStar_Syntax_Print.term_to_string
                                                  (FStar_Pervasives_Native.fst
                                                     y).FStar_Syntax_Syntax.sort in
                                              let uu____13388 =
                                                let uu____13391 =
                                                  names_to_string fvs in
                                                let uu____13392 =
                                                  let uu____13395 =
                                                    names_to_string
                                                      pattern_var_set in
                                                  [uu____13395] in
                                                uu____13391 :: uu____13392 in
                                              uu____13387 :: uu____13388 in
                                            uu____13383 :: uu____13384 in
                                          uu____13367 :: uu____13380 in
                                        FStar_Util.print
                                          "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                          uu____13364);
                                   aux pat_args pat_args_set pattern_vars
                                     pattern_var_set (formal :: seen_formals)
                                     formals1 res_t tl1)
                                else
                                  (let uu____13397 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst y)
                                       pat_args_set in
                                   let uu____13400 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst formal)
                                       pattern_var_set in
                                   aux (y :: pat_args) uu____13397 (formal ::
                                     pattern_vars) uu____13400 (formal ::
                                     seen_formals) formals1 res_t tl1)))))
                  | ([], uu____13407::uu____13408) ->
                      let uu____13439 =
                        let uu____13452 =
                          FStar_TypeChecker_Normalize.unfold_whnf env res_t in
                        FStar_Syntax_Util.arrow_formals uu____13452 in
                      (match uu____13439 with
                       | (more_formals, res_t1) ->
                           (match more_formals with
                            | [] -> FStar_Pervasives_Native.None
                            | uu____13491 ->
                                aux pat_args pat_args_set pattern_vars
                                  pattern_var_set seen_formals more_formals
                                  res_t1 args1))
                  | (uu____13498::uu____13499, []) ->
                      FStar_Pervasives_Native.None) in
               let uu____13522 =
                 let uu____13535 =
                   FStar_TypeChecker_Normalize.unfold_whnf env k in
                 FStar_Syntax_Util.arrow_formals uu____13535 in
               (match uu____13522 with
                | (all_formals, res_t) ->
                    (debug1
                       (fun uu____13571 ->
                          let uu____13572 =
                            FStar_Syntax_Print.term_to_string t in
                          let uu____13573 =
                            FStar_Syntax_Print.binders_to_string ", "
                              all_formals in
                          let uu____13574 =
                            FStar_Syntax_Print.term_to_string res_t in
                          let uu____13575 =
                            FStar_Syntax_Print.args_to_string args in
                          FStar_Util.print4
                            "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                            uu____13572 uu____13573 uu____13574 uu____13575);
                     (let uu____13576 = FStar_Syntax_Syntax.new_bv_set () in
                      let uu____13579 = FStar_Syntax_Syntax.new_bv_set () in
                      aux [] uu____13576 [] uu____13579 [] all_formals res_t
                        args))) in
         let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
           let uu____13613 = lhs in
           match uu____13613 with
           | (t1, uv, k_uv, args_lhs) ->
               let sol =
                 match pat_vars1 with
                 | [] -> rhs
                 | uu____13623 ->
                     let uu____13624 = sn_binders env1 pat_vars1 in
                     u_abs k_uv uu____13624 rhs in
               let wl2 =
                 solve_prob orig FStar_Pervasives_Native.None
                   [TERM ((uv, k_uv), sol)] wl1 in
               solve env1 wl2 in
         let imitate orig env1 wl1 p =
           let uu____13647 = p in
           match uu____13647 with
           | (((u, k), xs, c), ps, (h, uu____13658, qs)) ->
               let xs1 = sn_binders env1 xs in
               let r = FStar_TypeChecker_Env.get_range env1 in
               let uu____13740 = imitation_sub_probs orig env1 xs1 ps qs in
               (match uu____13740 with
                | (sub_probs, gs_xs, formula) ->
                    let im =
                      let uu____13763 = h gs_xs in
                      let uu____13764 =
                        FStar_All.pipe_right
                          (FStar_Syntax_Util.residual_comp_of_comp c)
                          (fun _0_57 -> FStar_Pervasives_Native.Some _0_57) in
                      FStar_Syntax_Util.abs xs1 uu____13763 uu____13764 in
                    ((let uu____13770 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____13770
                      then
                        let uu____13771 =
                          let uu____13774 =
                            let uu____13775 =
                              FStar_List.map tc_to_string gs_xs in
                            FStar_All.pipe_right uu____13775
                              (FStar_String.concat "\n\t>") in
                          let uu____13780 =
                            let uu____13783 =
                              FStar_Syntax_Print.binders_to_string ", " xs1 in
                            let uu____13784 =
                              let uu____13787 =
                                FStar_Syntax_Print.comp_to_string c in
                              let uu____13788 =
                                let uu____13791 =
                                  FStar_Syntax_Print.term_to_string im in
                                let uu____13792 =
                                  let uu____13795 =
                                    FStar_Syntax_Print.tag_of_term im in
                                  let uu____13796 =
                                    let uu____13799 =
                                      let uu____13800 =
                                        FStar_List.map (prob_to_string env1)
                                          sub_probs in
                                      FStar_All.pipe_right uu____13800
                                        (FStar_String.concat ", ") in
                                    let uu____13805 =
                                      let uu____13808 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env1 formula in
                                      [uu____13808] in
                                    uu____13799 :: uu____13805 in
                                  uu____13795 :: uu____13796 in
                                uu____13791 :: uu____13792 in
                              uu____13787 :: uu____13788 in
                            uu____13783 :: uu____13784 in
                          uu____13774 :: uu____13780 in
                        FStar_Util.print
                          "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                          uu____13771
                      else ());
                     def_check_closed (p_loc orig) "imitate" im;
                     (let wl2 =
                        solve_prob orig
                          (FStar_Pervasives_Native.Some formula)
                          [TERM ((u, k), im)] wl1 in
                      solve env1 (attempt sub_probs wl2)))) in
         let imitate' orig env1 wl1 uu___114_13830 =
           match uu___114_13830 with
           | FStar_Pervasives_Native.None ->
               giveup env1 "unable to compute subterms" orig
           | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
         let project orig env1 wl1 i p =
           let uu____13862 = p in
           match uu____13862 with
           | ((u, xs, c), ps, (h, matches, qs)) ->
               let r = FStar_TypeChecker_Env.get_range env1 in
               let uu____13953 = FStar_List.nth ps i in
               (match uu____13953 with
                | (pi, uu____13957) ->
                    let uu____13962 = FStar_List.nth xs i in
                    (match uu____13962 with
                     | (xi, uu____13974) ->
                         let rec gs k =
                           let uu____13987 =
                             let uu____14000 =
                               FStar_TypeChecker_Normalize.unfold_whnf env1 k in
                             FStar_Syntax_Util.arrow_formals uu____14000 in
                           match uu____13987 with
                           | (bs, k1) ->
                               let rec aux subst1 bs1 =
                                 match bs1 with
                                 | [] -> ([], [])
                                 | (a, uu____14075)::tl1 ->
                                     let k_a =
                                       FStar_Syntax_Subst.subst subst1
                                         a.FStar_Syntax_Syntax.sort in
                                     let uu____14088 = new_uvar r xs k_a in
                                     (match uu____14088 with
                                      | (gi_xs, gi) ->
                                          let gi_xs1 =
                                            FStar_TypeChecker_Normalize.eta_expand
                                              env1 gi_xs in
                                          let gi_ps =
                                            FStar_Syntax_Syntax.mk_Tm_app gi
                                              ps FStar_Pervasives_Native.None
                                              r in
                                          let subst2 =
                                            (FStar_Syntax_Syntax.NT
                                               (a, gi_xs1))
                                            :: subst1 in
                                          let uu____14110 = aux subst2 tl1 in
                                          (match uu____14110 with
                                           | (gi_xs', gi_ps') ->
                                               let uu____14137 =
                                                 let uu____14140 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_xs1 in
                                                 uu____14140 :: gi_xs' in
                                               let uu____14141 =
                                                 let uu____14144 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_ps in
                                                 uu____14144 :: gi_ps' in
                                               (uu____14137, uu____14141))) in
                               aux [] bs in
                         let uu____14149 =
                           let uu____14150 = matches pi in
                           FStar_All.pipe_left Prims.op_Negation uu____14150 in
                         if uu____14149
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____14154 = gs xi.FStar_Syntax_Syntax.sort in
                            match uu____14154 with
                            | (g_xs, uu____14166) ->
                                let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                                let proj =
                                  let uu____14177 =
                                    FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                      FStar_Pervasives_Native.None r in
                                  let uu____14178 =
                                    FStar_All.pipe_right
                                      (FStar_Syntax_Util.residual_comp_of_comp
                                         c)
                                      (fun _0_58 ->
                                         FStar_Pervasives_Native.Some _0_58) in
                                  FStar_Syntax_Util.abs xs uu____14177
                                    uu____14178 in
                                let sub1 =
                                  let uu____14184 =
                                    let uu____14189 = p_scope orig in
                                    let uu____14190 =
                                      FStar_Syntax_Syntax.mk_Tm_app proj ps
                                        FStar_Pervasives_Native.None r in
                                    let uu____14193 =
                                      let uu____14196 =
                                        FStar_List.map
                                          (fun uu____14211 ->
                                             match uu____14211 with
                                             | (uu____14220, uu____14221, y)
                                                 -> y) qs in
                                      FStar_All.pipe_left h uu____14196 in
                                    mk_problem uu____14189 orig uu____14190
                                      (p_rel orig) uu____14193
                                      FStar_Pervasives_Native.None
                                      "projection" in
                                  FStar_All.pipe_left
                                    (fun _0_59 ->
                                       FStar_TypeChecker_Common.TProb _0_59)
                                    uu____14184 in
                                ((let uu____14236 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env1)
                                      (FStar_Options.Other "Rel") in
                                  if uu____14236
                                  then
                                    let uu____14237 =
                                      FStar_Syntax_Print.term_to_string proj in
                                    let uu____14238 =
                                      prob_to_string env1 sub1 in
                                    FStar_Util.print2
                                      "Projecting %s\n\tsubprob=%s\n"
                                      uu____14237 uu____14238
                                  else ());
                                 (let wl2 =
                                    let uu____14241 =
                                      let uu____14244 =
                                        FStar_All.pipe_left
                                          FStar_Pervasives_Native.fst
                                          (p_guard sub1) in
                                      FStar_Pervasives_Native.Some
                                        uu____14244 in
                                    solve_prob orig uu____14241
                                      [TERM (u, proj)] wl1 in
                                  let uu____14253 =
                                    solve env1 (attempt [sub1] wl2) in
                                  FStar_All.pipe_left
                                    (fun _0_60 ->
                                       FStar_Pervasives_Native.Some _0_60)
                                    uu____14253))))) in
         let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
           let uu____14284 = lhs in
           match uu____14284 with
           | ((t1, uv, k_uv, args_lhs), maybe_pat_vars) ->
               let subterms ps =
                 let uu____14320 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                 match uu____14320 with
                 | (xs, c) ->
                     if (FStar_List.length xs) = (FStar_List.length ps)
                     then
                       let uu____14353 =
                         let uu____14400 = decompose env t2 in
                         (((uv, k_uv), xs, c), ps, uu____14400) in
                       FStar_Pervasives_Native.Some uu____14353
                     else
                       (let rec elim k args =
                          let k1 =
                            FStar_TypeChecker_Normalize.unfold_whnf env k in
                          let uu____14544 =
                            let uu____14551 =
                              let uu____14552 =
                                FStar_Syntax_Subst.compress k1 in
                              uu____14552.FStar_Syntax_Syntax.n in
                            (uu____14551, args) in
                          match uu____14544 with
                          | (uu____14563, []) ->
                              let uu____14566 =
                                let uu____14577 =
                                  FStar_Syntax_Syntax.mk_Total k1 in
                                ([], uu____14577) in
                              FStar_Pervasives_Native.Some uu____14566
                          | (FStar_Syntax_Syntax.Tm_uvar uu____14598,
                             uu____14599) ->
                              let uu____14620 =
                                FStar_Syntax_Util.head_and_args k1 in
                              (match uu____14620 with
                               | (uv1, uv_args) ->
                                   let uu____14663 =
                                     let uu____14664 =
                                       FStar_Syntax_Subst.compress uv1 in
                                     uu____14664.FStar_Syntax_Syntax.n in
                                   (match uu____14663 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar, uu____14674) ->
                                        let uu____14699 =
                                          pat_vars env [] uv_args in
                                        (match uu____14699 with
                                         | FStar_Pervasives_Native.None ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____14726 ->
                                                       let uu____14727 =
                                                         let uu____14728 =
                                                           let uu____14729 =
                                                             let uu____14734
                                                               =
                                                               let uu____14735
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   () in
                                                               FStar_All.pipe_right
                                                                 uu____14735
                                                                 FStar_Pervasives_Native.fst in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____14734 in
                                                           FStar_Pervasives_Native.fst
                                                             uu____14729 in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____14728 in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____14727)) in
                                             let c1 =
                                               let uu____14745 =
                                                 let uu____14746 =
                                                   let uu____14751 =
                                                     let uu____14752 =
                                                       FStar_Syntax_Util.type_u
                                                         () in
                                                     FStar_All.pipe_right
                                                       uu____14752
                                                       FStar_Pervasives_Native.fst in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____14751 in
                                                 FStar_Pervasives_Native.fst
                                                   uu____14746 in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____14745 in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1 in
                                             let uv_sol =
                                               let uu____14765 =
                                                 let uu____14768 =
                                                   let uu____14769 =
                                                     let uu____14772 =
                                                       FStar_Syntax_Util.type_u
                                                         () in
                                                     FStar_All.pipe_right
                                                       uu____14772
                                                       FStar_Pervasives_Native.fst in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____14769 in
                                                 FStar_Pervasives_Native.Some
                                                   uu____14768 in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____14765 in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____14791 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_app uu____14796,
                             uu____14797) ->
                              let uu____14816 =
                                FStar_Syntax_Util.head_and_args k1 in
                              (match uu____14816 with
                               | (uv1, uv_args) ->
                                   let uu____14859 =
                                     let uu____14860 =
                                       FStar_Syntax_Subst.compress uv1 in
                                     uu____14860.FStar_Syntax_Syntax.n in
                                   (match uu____14859 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar, uu____14870) ->
                                        let uu____14895 =
                                          pat_vars env [] uv_args in
                                        (match uu____14895 with
                                         | FStar_Pervasives_Native.None ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____14922 ->
                                                       let uu____14923 =
                                                         let uu____14924 =
                                                           let uu____14925 =
                                                             let uu____14930
                                                               =
                                                               let uu____14931
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   () in
                                                               FStar_All.pipe_right
                                                                 uu____14931
                                                                 FStar_Pervasives_Native.fst in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____14930 in
                                                           FStar_Pervasives_Native.fst
                                                             uu____14925 in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____14924 in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____14923)) in
                                             let c1 =
                                               let uu____14941 =
                                                 let uu____14942 =
                                                   let uu____14947 =
                                                     let uu____14948 =
                                                       FStar_Syntax_Util.type_u
                                                         () in
                                                     FStar_All.pipe_right
                                                       uu____14948
                                                       FStar_Pervasives_Native.fst in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____14947 in
                                                 FStar_Pervasives_Native.fst
                                                   uu____14942 in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____14941 in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1 in
                                             let uv_sol =
                                               let uu____14961 =
                                                 let uu____14964 =
                                                   let uu____14965 =
                                                     let uu____14968 =
                                                       FStar_Syntax_Util.type_u
                                                         () in
                                                     FStar_All.pipe_right
                                                       uu____14968
                                                       FStar_Pervasives_Native.fst in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____14965 in
                                                 FStar_Pervasives_Native.Some
                                                   uu____14964 in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____14961 in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____14987 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_arrow (xs1, c1),
                             uu____14994) ->
                              let n_args = FStar_List.length args in
                              let n_xs = FStar_List.length xs1 in
                              if n_xs = n_args
                              then
                                let uu____15035 =
                                  FStar_Syntax_Subst.open_comp xs1 c1 in
                                FStar_All.pipe_right uu____15035
                                  (fun _0_61 ->
                                     FStar_Pervasives_Native.Some _0_61)
                              else
                                if n_xs < n_args
                                then
                                  (let uu____15071 =
                                     FStar_Util.first_N n_xs args in
                                   match uu____15071 with
                                   | (args1, rest) ->
                                       let uu____15100 =
                                         FStar_Syntax_Subst.open_comp xs1 c1 in
                                       (match uu____15100 with
                                        | (xs2, c2) ->
                                            let uu____15113 =
                                              elim
                                                (FStar_Syntax_Util.comp_result
                                                   c2) rest in
                                            FStar_Util.bind_opt uu____15113
                                              (fun uu____15137 ->
                                                 match uu____15137 with
                                                 | (xs', c3) ->
                                                     FStar_Pervasives_Native.Some
                                                       ((FStar_List.append
                                                           xs2 xs'), c3))))
                                else
                                  (let uu____15177 =
                                     FStar_Util.first_N n_args xs1 in
                                   match uu____15177 with
                                   | (xs2, rest) ->
                                       let t =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))
                                           FStar_Pervasives_Native.None
                                           k1.FStar_Syntax_Syntax.pos in
                                       let uu____15245 =
                                         let uu____15250 =
                                           FStar_Syntax_Syntax.mk_Total t in
                                         FStar_Syntax_Subst.open_comp xs2
                                           uu____15250 in
                                       FStar_All.pipe_right uu____15245
                                         (fun _0_62 ->
                                            FStar_Pervasives_Native.Some
                                              _0_62))
                          | uu____15265 ->
                              let uu____15272 =
                                let uu____15277 =
                                  let uu____15278 =
                                    FStar_Syntax_Print.uvar_to_string uv in
                                  let uu____15279 =
                                    FStar_Syntax_Print.term_to_string k1 in
                                  let uu____15280 =
                                    FStar_Syntax_Print.term_to_string k_uv in
                                  FStar_Util.format3
                                    "Impossible: ill-typed application %s : %s\n\t%s"
                                    uu____15278 uu____15279 uu____15280 in
                                (FStar_Errors.Fatal_IllTyped, uu____15277) in
                              FStar_Errors.raise_error uu____15272
                                t1.FStar_Syntax_Syntax.pos in
                        let uu____15287 = elim k_uv ps in
                        FStar_Util.bind_opt uu____15287
                          (fun uu____15342 ->
                             match uu____15342 with
                             | (xs1, c1) ->
                                 let uu____15391 =
                                   let uu____15432 = decompose env t2 in
                                   (((uv, k_uv), xs1, c1), ps, uu____15432) in
                                 FStar_Pervasives_Native.Some uu____15391)) in
               let imitate_or_project n1 lhs1 rhs stopt =
                 let fail1 uu____15553 =
                   giveup env
                     "flex-rigid case failed all backtracking attempts" orig in
                 let rec try_project st i =
                   if i >= n1
                   then fail1 ()
                   else
                     (let tx = FStar_Syntax_Unionfind.new_transaction () in
                      let uu____15567 = project orig env wl1 i st in
                      match uu____15567 with
                      | FStar_Pervasives_Native.None ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____15581) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol) in
                 if FStar_Option.isSome stopt
                 then
                   let st = FStar_Util.must stopt in
                   let tx = FStar_Syntax_Unionfind.new_transaction () in
                   let uu____15596 = imitate orig env wl1 st in
                   match uu____15596 with
                   | Failed uu____15601 ->
                       (FStar_Syntax_Unionfind.rollback tx;
                        try_project st (Prims.parse_int "0"))
                   | sol -> sol
                 else fail1 () in
               let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                 let uu____15632 =
                   force_quasi_pattern FStar_Pervasives_Native.None lhs1 in
                 match uu____15632 with
                 | FStar_Pervasives_Native.None ->
                     imitate_or_project n1 lhs1 rhs stopt
                 | FStar_Pervasives_Native.Some (sol, forced_lhs_pattern) ->
                     let uu____15655 = forced_lhs_pattern in
                     (match uu____15655 with
                      | (lhs_t, uu____15657, uu____15658, uu____15659) ->
                          ((let uu____15661 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "Rel") in
                            if uu____15661
                            then
                              let uu____15662 = lhs1 in
                              match uu____15662 with
                              | (t0, uu____15664, uu____15665, uu____15666)
                                  ->
                                  let uu____15667 = forced_lhs_pattern in
                                  (match uu____15667 with
                                   | (t11, uu____15669, uu____15670,
                                      uu____15671) ->
                                       let uu____15672 =
                                         FStar_Syntax_Print.term_to_string t0 in
                                       let uu____15673 =
                                         FStar_Syntax_Print.term_to_string
                                           t11 in
                                       FStar_Util.print2
                                         "force_quasi_pattern succeeded, turning %s into %s\n"
                                         uu____15672 uu____15673)
                            else ());
                           (let rhs_vars = FStar_Syntax_Free.names rhs in
                            let lhs_vars = FStar_Syntax_Free.names lhs_t in
                            let uu____15681 =
                              FStar_Util.set_is_subset_of rhs_vars lhs_vars in
                            if uu____15681
                            then
                              ((let uu____15683 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel") in
                                if uu____15683
                                then
                                  let uu____15684 =
                                    FStar_Syntax_Print.term_to_string rhs in
                                  let uu____15685 = names_to_string rhs_vars in
                                  let uu____15686 = names_to_string lhs_vars in
                                  FStar_Util.print3
                                    "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                    uu____15684 uu____15685 uu____15686
                                else ());
                               (let tx =
                                  FStar_Syntax_Unionfind.new_transaction () in
                                let wl2 =
                                  extend_solution (p_pid orig) [sol] wl1 in
                                let uu____15690 =
                                  let uu____15691 =
                                    FStar_TypeChecker_Common.as_tprob orig in
                                  solve_t env uu____15691 wl2 in
                                match uu____15690 with
                                | Failed uu____15692 ->
                                    (FStar_Syntax_Unionfind.rollback tx;
                                     imitate_or_project n1 lhs1 rhs stopt)
                                | sol1 -> sol1))
                            else
                              ((let uu____15701 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel") in
                                if uu____15701
                                then
                                  FStar_Util.print_string
                                    "fvar check failed for quasi pattern ... im/proj\n"
                                else ());
                               imitate_or_project n1 lhs1 rhs stopt)))) in
               let check_head fvs1 t21 =
                 let uu____15714 = FStar_Syntax_Util.head_and_args t21 in
                 match uu____15714 with
                 | (hd1, uu____15730) ->
                     (match hd1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_arrow uu____15751 -> true
                      | FStar_Syntax_Syntax.Tm_constant uu____15764 -> true
                      | FStar_Syntax_Syntax.Tm_abs uu____15765 -> true
                      | uu____15782 ->
                          let fvs_hd = FStar_Syntax_Free.names hd1 in
                          let uu____15786 =
                            FStar_Util.set_is_subset_of fvs_hd fvs1 in
                          if uu____15786
                          then true
                          else
                            ((let uu____15789 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel") in
                              if uu____15789
                              then
                                let uu____15790 = names_to_string fvs_hd in
                                FStar_Util.print1 "Free variables are %s\n"
                                  uu____15790
                              else ());
                             false)) in
               (match maybe_pat_vars with
                | FStar_Pervasives_Native.Some vars ->
                    let t11 = sn env t1 in
                    let t21 = sn env t2 in
                    let lhs1 = (t11, uv, k_uv, args_lhs) in
                    let fvs1 = FStar_Syntax_Free.names t11 in
                    let fvs2 = FStar_Syntax_Free.names t21 in
                    let uu____15810 = occurs_check env wl1 (uv, k_uv) t21 in
                    (match uu____15810 with
                     | (occurs_ok, msg) ->
                         if Prims.op_Negation occurs_ok
                         then
                           let uu____15823 =
                             let uu____15824 = FStar_Option.get msg in
                             Prims.strcat "occurs-check failed: " uu____15824 in
                           giveup_or_defer1 orig uu____15823
                         else
                           (let uu____15826 =
                              FStar_Util.set_is_subset_of fvs2 fvs1 in
                            if uu____15826
                            then
                              let uu____15827 =
                                ((Prims.op_Negation patterns_only) &&
                                   (FStar_Syntax_Util.is_function_typ t21))
                                  &&
                                  ((p_rel orig) <>
                                     FStar_TypeChecker_Common.EQ) in
                              (if uu____15827
                               then
                                 let uu____15828 = subterms args_lhs in
                                 imitate' orig env wl1 uu____15828
                               else
                                 ((let uu____15833 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____15833
                                   then
                                     let uu____15834 =
                                       FStar_Syntax_Print.term_to_string t11 in
                                     let uu____15835 = names_to_string fvs1 in
                                     let uu____15836 = names_to_string fvs2 in
                                     FStar_Util.print3
                                       "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                       uu____15834 uu____15835 uu____15836
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
                                (let uu____15840 =
                                   (Prims.op_Negation patterns_only) &&
                                     (check_head fvs1 t21) in
                                 if uu____15840
                                 then
                                   ((let uu____15842 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel") in
                                     if uu____15842
                                     then
                                       let uu____15843 =
                                         FStar_Syntax_Print.term_to_string
                                           t11 in
                                       let uu____15844 = names_to_string fvs1 in
                                       let uu____15845 = names_to_string fvs2 in
                                       FStar_Util.print3
                                         "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                         uu____15843 uu____15844 uu____15845
                                     else ());
                                    (let uu____15847 = subterms args_lhs in
                                     imitate_or_project
                                       (FStar_List.length args_lhs) lhs1 t21
                                       uu____15847))
                                 else
                                   giveup env
                                     "free-variable check failed on a non-redex"
                                     orig)))
                | FStar_Pervasives_Native.None when patterns_only ->
                    giveup env "not a pattern" orig
                | FStar_Pervasives_Native.None ->
                    if wl1.defer_ok
                    then solve env (defer "not a pattern" orig wl1)
                    else
                      (let uu____15858 =
                         let uu____15859 = FStar_Syntax_Free.names t1 in
                         check_head uu____15859 t2 in
                       if uu____15858
                       then
                         let n_args_lhs = FStar_List.length args_lhs in
                         ((let uu____15870 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15870
                           then
                             let uu____15871 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____15872 =
                               FStar_Util.string_of_int n_args_lhs in
                             FStar_Util.print2
                               "Not a pattern (%s) ... (lhs has %s args)\n"
                               uu____15871 uu____15872
                           else ());
                          (let uu____15880 = subterms args_lhs in
                           pattern_eq_imitate_or_project n_args_lhs
                             (FStar_Pervasives_Native.fst lhs) t2 uu____15880))
                       else giveup env "head-symbol is free" orig)) in
         let flex_flex1 orig lhs rhs =
           if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
           then solve env (defer "flex-flex deferred" orig wl)
           else
             (let solve_both_pats wl1 uu____15957 uu____15958 r =
                match (uu____15957, uu____15958) with
                | ((u1, k1, xs, args1), (u2, k2, ys, args2)) ->
                    let uu____16156 =
                      (FStar_Syntax_Unionfind.equiv u1 u2) &&
                        (binders_eq xs ys) in
                    if uu____16156
                    then
                      let uu____16157 =
                        solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                      solve env uu____16157
                    else
                      (let xs1 = sn_binders env xs in
                       let ys1 = sn_binders env ys in
                       let zs = intersect_vars xs1 ys1 in
                       (let uu____16181 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel") in
                        if uu____16181
                        then
                          let uu____16182 =
                            FStar_Syntax_Print.binders_to_string ", " xs1 in
                          let uu____16183 =
                            FStar_Syntax_Print.binders_to_string ", " ys1 in
                          let uu____16184 =
                            FStar_Syntax_Print.binders_to_string ", " zs in
                          let uu____16185 =
                            FStar_Syntax_Print.term_to_string k1 in
                          let uu____16186 =
                            FStar_Syntax_Print.term_to_string k2 in
                          FStar_Util.print5
                            "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                            uu____16182 uu____16183 uu____16184 uu____16185
                            uu____16186
                        else ());
                       (let subst_k k xs2 args =
                          let xs_len = FStar_List.length xs2 in
                          let args_len = FStar_List.length args in
                          if xs_len = args_len
                          then
                            let uu____16246 =
                              FStar_Syntax_Util.subst_of_list xs2 args in
                            FStar_Syntax_Subst.subst uu____16246 k
                          else
                            if args_len < xs_len
                            then
                              (let uu____16260 =
                                 FStar_Util.first_N args_len xs2 in
                               match uu____16260 with
                               | (xs3, xs_rest) ->
                                   let k3 =
                                     let uu____16314 =
                                       FStar_Syntax_Syntax.mk_GTotal k in
                                     FStar_Syntax_Util.arrow xs_rest
                                       uu____16314 in
                                   let uu____16317 =
                                     FStar_Syntax_Util.subst_of_list xs3 args in
                                   FStar_Syntax_Subst.subst uu____16317 k3)
                            else
                              (let uu____16321 =
                                 let uu____16322 =
                                   FStar_Syntax_Print.term_to_string k in
                                 let uu____16323 =
                                   FStar_Syntax_Print.binders_to_string ", "
                                     xs2 in
                                 let uu____16324 =
                                   FStar_Syntax_Print.args_to_string args in
                                 FStar_Util.format3
                                   "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                   uu____16322 uu____16323 uu____16324 in
                               failwith uu____16321) in
                        let uu____16325 =
                          let uu____16332 =
                            let uu____16345 =
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Normalize.Beta] env k1 in
                            FStar_Syntax_Util.arrow_formals uu____16345 in
                          match uu____16332 with
                          | (bs, k1') ->
                              let uu____16370 =
                                let uu____16383 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env k2 in
                                FStar_Syntax_Util.arrow_formals uu____16383 in
                              (match uu____16370 with
                               | (cs, k2') ->
                                   let k1'_xs = subst_k k1' bs args1 in
                                   let k2'_ys = subst_k k2' cs args2 in
                                   let sub_prob =
                                     let uu____16411 =
                                       let uu____16416 = p_scope orig in
                                       mk_problem uu____16416 orig k1'_xs
                                         FStar_TypeChecker_Common.EQ k2'_ys
                                         FStar_Pervasives_Native.None
                                         "flex-flex kinding" in
                                     FStar_All.pipe_left
                                       (fun _0_63 ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_63) uu____16411 in
                                   let uu____16421 =
                                     let uu____16426 =
                                       let uu____16427 =
                                         FStar_Syntax_Subst.compress k1' in
                                       uu____16427.FStar_Syntax_Syntax.n in
                                     let uu____16430 =
                                       let uu____16431 =
                                         FStar_Syntax_Subst.compress k2' in
                                       uu____16431.FStar_Syntax_Syntax.n in
                                     (uu____16426, uu____16430) in
                                   (match uu____16421 with
                                    | (FStar_Syntax_Syntax.Tm_type
                                       uu____16440, uu____16441) ->
                                        (k1'_xs, [sub_prob])
                                    | (uu____16444,
                                       FStar_Syntax_Syntax.Tm_type
                                       uu____16445) -> (k2'_ys, [sub_prob])
                                    | uu____16448 ->
                                        let uu____16453 =
                                          FStar_Syntax_Util.type_u () in
                                        (match uu____16453 with
                                         | (t, uu____16465) ->
                                             let uu____16466 =
                                               new_uvar r zs t in
                                             (match uu____16466 with
                                              | (k_zs, uu____16478) ->
                                                  let kprob =
                                                    let uu____16480 =
                                                      let uu____16485 =
                                                        p_scope orig in
                                                      mk_problem uu____16485
                                                        orig k1'_xs
                                                        FStar_TypeChecker_Common.EQ
                                                        k_zs
                                                        FStar_Pervasives_Native.None
                                                        "flex-flex kinding" in
                                                    FStar_All.pipe_left
                                                      (fun _0_64 ->
                                                         FStar_TypeChecker_Common.TProb
                                                           _0_64) uu____16480 in
                                                  (k_zs, [sub_prob; kprob]))))) in
                        match uu____16325 with
                        | (k_u', sub_probs) ->
                            let uu____16498 =
                              let uu____16509 =
                                let uu____16510 = new_uvar r zs k_u' in
                                FStar_All.pipe_left
                                  FStar_Pervasives_Native.fst uu____16510 in
                              let uu____16519 =
                                let uu____16522 =
                                  FStar_Syntax_Syntax.mk_Total k_u' in
                                FStar_Syntax_Util.arrow xs1 uu____16522 in
                              let uu____16525 =
                                let uu____16528 =
                                  FStar_Syntax_Syntax.mk_Total k_u' in
                                FStar_Syntax_Util.arrow ys1 uu____16528 in
                              (uu____16509, uu____16519, uu____16525) in
                            (match uu____16498 with
                             | (u_zs, knew1, knew2) ->
                                 let sub1 = u_abs knew1 xs1 u_zs in
                                 let uu____16547 =
                                   occurs_check env wl1 (u1, k1) sub1 in
                                 (match uu____16547 with
                                  | (occurs_ok, msg) ->
                                      if Prims.op_Negation occurs_ok
                                      then
                                        giveup_or_defer1 orig
                                          "flex-flex: failed occcurs check"
                                      else
                                        (let sol1 = TERM ((u1, k1), sub1) in
                                         let uu____16566 =
                                           FStar_Syntax_Unionfind.equiv u1 u2 in
                                         if uu____16566
                                         then
                                           let wl2 =
                                             solve_prob orig
                                               FStar_Pervasives_Native.None
                                               [sol1] wl1 in
                                           solve env wl2
                                         else
                                           (let sub2 = u_abs knew2 ys1 u_zs in
                                            let uu____16570 =
                                              occurs_check env wl1 (u2, k2)
                                                sub2 in
                                            match uu____16570 with
                                            | (occurs_ok1, msg1) ->
                                                if
                                                  Prims.op_Negation
                                                    occurs_ok1
                                                then
                                                  giveup_or_defer1 orig
                                                    "flex-flex: failed occurs check"
                                                else
                                                  (let sol2 =
                                                     TERM ((u2, k2), sub2) in
                                                   let wl2 =
                                                     solve_prob orig
                                                       FStar_Pervasives_Native.None
                                                       [sol1; sol2] wl1 in
                                                   solve env
                                                     (attempt sub_probs wl2)))))))) in
              let solve_one_pat uu____16623 uu____16624 =
                match (uu____16623, uu____16624) with
                | ((t1, u1, k1, xs), (t2, u2, k2, args2)) ->
                    ((let uu____16742 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel") in
                      if uu____16742
                      then
                        let uu____16743 =
                          FStar_Syntax_Print.term_to_string t1 in
                        let uu____16744 =
                          FStar_Syntax_Print.term_to_string t2 in
                        FStar_Util.print2
                          "Trying flex-flex one pattern (%s) with %s\n"
                          uu____16743 uu____16744
                      else ());
                     (let uu____16746 = FStar_Syntax_Unionfind.equiv u1 u2 in
                      if uu____16746
                      then
                        let sub_probs =
                          FStar_List.map2
                            (fun uu____16765 ->
                               fun uu____16766 ->
                                 match (uu____16765, uu____16766) with
                                 | ((a, uu____16784), (t21, uu____16786)) ->
                                     let uu____16795 =
                                       let uu____16800 = p_scope orig in
                                       let uu____16801 =
                                         FStar_Syntax_Syntax.bv_to_name a in
                                       mk_problem uu____16800 orig
                                         uu____16801
                                         FStar_TypeChecker_Common.EQ t21
                                         FStar_Pervasives_Native.None
                                         "flex-flex index" in
                                     FStar_All.pipe_right uu____16795
                                       (fun _0_65 ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_65)) xs args2 in
                        let guard =
                          let uu____16807 =
                            FStar_List.map
                              (fun p ->
                                 FStar_All.pipe_right (p_guard p)
                                   FStar_Pervasives_Native.fst) sub_probs in
                          FStar_Syntax_Util.mk_conj_l uu____16807 in
                        let wl1 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl in
                        solve env (attempt sub_probs wl1)
                      else
                        (let t21 = sn env t2 in
                         let rhs_vars = FStar_Syntax_Free.names t21 in
                         let uu____16822 = occurs_check env wl (u1, k1) t21 in
                         match uu____16822 with
                         | (occurs_ok, uu____16830) ->
                             let lhs_vars =
                               FStar_Syntax_Free.names_of_binders xs in
                             let uu____16838 =
                               occurs_ok &&
                                 (FStar_Util.set_is_subset_of rhs_vars
                                    lhs_vars) in
                             if uu____16838
                             then
                               let sol =
                                 let uu____16840 =
                                   let uu____16849 = u_abs k1 xs t21 in
                                   ((u1, k1), uu____16849) in
                                 TERM uu____16840 in
                               let wl1 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [sol] wl in
                               solve env wl1
                             else
                               (let uu____16856 =
                                  occurs_ok &&
                                    (FStar_All.pipe_left Prims.op_Negation
                                       wl.defer_ok) in
                                if uu____16856
                                then
                                  let uu____16857 =
                                    force_quasi_pattern
                                      (FStar_Pervasives_Native.Some xs)
                                      (t21, u2, k2, args2) in
                                  match uu____16857 with
                                  | FStar_Pervasives_Native.None ->
                                      giveup_or_defer1 orig
                                        "flex-flex constraint"
                                  | FStar_Pervasives_Native.Some
                                      (sol, (uu____16881, u21, k21, ys)) ->
                                      let wl1 =
                                        extend_solution (p_pid orig) [sol] wl in
                                      ((let uu____16907 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other
                                               "QuasiPattern") in
                                        if uu____16907
                                        then
                                          let uu____16908 =
                                            uvi_to_string env sol in
                                          FStar_Util.print1
                                            "flex-flex quasi pattern (2): %s\n"
                                            uu____16908
                                        else ());
                                       (match orig with
                                        | FStar_TypeChecker_Common.TProb p ->
                                            solve_t env p wl1
                                        | uu____16915 ->
                                            giveup env "impossible" orig))
                                else
                                  giveup_or_defer1 orig
                                    "flex-flex constraint")))) in
              let uu____16917 = lhs in
              match uu____16917 with
              | (t1, u1, k1, args1) ->
                  let uu____16922 = rhs in
                  (match uu____16922 with
                   | (t2, u2, k2, args2) ->
                       let maybe_pat_vars1 = pat_vars env [] args1 in
                       let maybe_pat_vars2 = pat_vars env [] args2 in
                       let r = t2.FStar_Syntax_Syntax.pos in
                       (match (maybe_pat_vars1, maybe_pat_vars2) with
                        | (FStar_Pervasives_Native.Some xs,
                           FStar_Pervasives_Native.Some ys) ->
                            solve_both_pats wl (u1, k1, xs, args1)
                              (u2, k2, ys, args2) t2.FStar_Syntax_Syntax.pos
                        | (FStar_Pervasives_Native.Some xs,
                           FStar_Pervasives_Native.None) ->
                            solve_one_pat (t1, u1, k1, xs) rhs
                        | (FStar_Pervasives_Native.None,
                           FStar_Pervasives_Native.Some ys) ->
                            solve_one_pat (t2, u2, k2, ys) lhs
                        | uu____16962 ->
                            if wl.defer_ok
                            then
                              giveup_or_defer1 orig
                                "flex-flex: neither side is a pattern"
                            else
                              (let uu____16972 =
                                 force_quasi_pattern
                                   FStar_Pervasives_Native.None
                                   (t1, u1, k1, args1) in
                               match uu____16972 with
                               | FStar_Pervasives_Native.None ->
                                   giveup env
                                     "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                     orig
                               | FStar_Pervasives_Native.Some
                                   (sol, uu____16990) ->
                                   let wl1 =
                                     extend_solution (p_pid orig) [sol] wl in
                                   ((let uu____16997 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "QuasiPattern") in
                                     if uu____16997
                                     then
                                       let uu____16998 =
                                         uvi_to_string env sol in
                                       FStar_Util.print1
                                         "flex-flex quasi pattern (1): %s\n"
                                         uu____16998
                                     else ());
                                    (match orig with
                                     | FStar_TypeChecker_Common.TProb p ->
                                         solve_t env p wl1
                                     | uu____17005 ->
                                         giveup env "impossible" orig)))))) in
         let orig = FStar_TypeChecker_Common.TProb problem in
         def_check_prob "solve_t'.2" orig;
         (let uu____17008 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs in
          if uu____17008
          then
            let uu____17009 =
              solve_prob orig FStar_Pervasives_Native.None [] wl in
            solve env uu____17009
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs in
             let t2 = problem.FStar_TypeChecker_Common.rhs in
             let uu____17013 = FStar_Util.physical_equality t1 t2 in
             if uu____17013
             then
               let uu____17014 =
                 solve_prob orig FStar_Pervasives_Native.None [] wl in
               solve env uu____17014
             else
               ((let uu____17017 =
                   FStar_TypeChecker_Env.debug env
                     (FStar_Options.Other "RelCheck") in
                 if uu____17017
                 then
                   let uu____17018 =
                     FStar_Util.string_of_int
                       problem.FStar_TypeChecker_Common.pid in
                   let uu____17019 = FStar_Syntax_Print.tag_of_term t1 in
                   let uu____17020 = FStar_Syntax_Print.tag_of_term t2 in
                   FStar_Util.print3 "Attempting %s (%s - %s)\n" uu____17018
                     uu____17019 uu____17020
                 else ());
                (let r = FStar_TypeChecker_Env.get_range env in
                 match ((t1.FStar_Syntax_Syntax.n),
                         (t2.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.Tm_delayed uu____17023, uu____17024)
                     -> failwith "Impossible: terms were not compressed"
                 | (uu____17049, FStar_Syntax_Syntax.Tm_delayed uu____17050)
                     -> failwith "Impossible: terms were not compressed"
                 | (FStar_Syntax_Syntax.Tm_ascribed uu____17075, uu____17076)
                     ->
                     let uu____17103 =
                       let uu___151_17104 = problem in
                       let uu____17105 = FStar_Syntax_Util.unascribe t1 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___151_17104.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____17105;
                         FStar_TypeChecker_Common.relation =
                           (uu___151_17104.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___151_17104.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___151_17104.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___151_17104.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___151_17104.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___151_17104.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___151_17104.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___151_17104.FStar_TypeChecker_Common.rank)
                       } in
                     solve_t' env uu____17103 wl
                 | (FStar_Syntax_Syntax.Tm_meta uu____17106, uu____17107) ->
                     let uu____17114 =
                       let uu___152_17115 = problem in
                       let uu____17116 = FStar_Syntax_Util.unmeta t1 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___152_17115.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____17116;
                         FStar_TypeChecker_Common.relation =
                           (uu___152_17115.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___152_17115.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___152_17115.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___152_17115.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___152_17115.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___152_17115.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___152_17115.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___152_17115.FStar_TypeChecker_Common.rank)
                       } in
                     solve_t' env uu____17114 wl
                 | (uu____17117, FStar_Syntax_Syntax.Tm_ascribed uu____17118)
                     ->
                     let uu____17145 =
                       let uu___153_17146 = problem in
                       let uu____17147 = FStar_Syntax_Util.unascribe t2 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___153_17146.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___153_17146.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___153_17146.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____17147;
                         FStar_TypeChecker_Common.element =
                           (uu___153_17146.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___153_17146.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___153_17146.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___153_17146.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___153_17146.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___153_17146.FStar_TypeChecker_Common.rank)
                       } in
                     solve_t' env uu____17145 wl
                 | (uu____17148, FStar_Syntax_Syntax.Tm_meta uu____17149) ->
                     let uu____17156 =
                       let uu___154_17157 = problem in
                       let uu____17158 = FStar_Syntax_Util.unmeta t2 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___154_17157.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___154_17157.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___154_17157.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____17158;
                         FStar_TypeChecker_Common.element =
                           (uu___154_17157.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___154_17157.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___154_17157.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___154_17157.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___154_17157.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___154_17157.FStar_TypeChecker_Common.rank)
                       } in
                     solve_t' env uu____17156 wl
                 | (FStar_Syntax_Syntax.Tm_quoted (t11, uu____17160),
                    FStar_Syntax_Syntax.Tm_quoted (t21, uu____17162)) ->
                     let uu____17171 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl in
                     solve env uu____17171
                 | (FStar_Syntax_Syntax.Tm_bvar uu____17172, uu____17173) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (uu____17174, FStar_Syntax_Syntax.Tm_bvar uu____17175) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (FStar_Syntax_Syntax.Tm_type u1,
                    FStar_Syntax_Syntax.Tm_type u2) ->
                     solve_one_universe_eq env orig u1 u2 wl
                 | (FStar_Syntax_Syntax.Tm_arrow (bs1, c1),
                    FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) ->
                     let mk_c c uu___115_17230 =
                       match uu___115_17230 with
                       | [] -> c
                       | bs ->
                           let uu____17252 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                               FStar_Pervasives_Native.None
                               c.FStar_Syntax_Syntax.pos in
                           FStar_Syntax_Syntax.mk_Total uu____17252 in
                     let uu____17261 =
                       match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                     (match uu____17261 with
                      | ((bs11, c11), (bs21, c21)) ->
                          solve_binders env bs11 bs21 orig wl
                            (fun scope ->
                               fun env1 ->
                                 fun subst1 ->
                                   let c12 =
                                     FStar_Syntax_Subst.subst_comp subst1 c11 in
                                   let c22 =
                                     FStar_Syntax_Subst.subst_comp subst1 c21 in
                                   let rel =
                                     let uu____17403 =
                                       FStar_Options.use_eq_at_higher_order
                                         () in
                                     if uu____17403
                                     then FStar_TypeChecker_Common.EQ
                                     else
                                       problem.FStar_TypeChecker_Common.relation in
                                   let uu____17405 =
                                     mk_problem scope orig c12 rel c22
                                       FStar_Pervasives_Native.None
                                       "function co-domain" in
                                   FStar_All.pipe_left
                                     (fun _0_66 ->
                                        FStar_TypeChecker_Common.CProb _0_66)
                                     uu____17405))
                 | (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1),
                    FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) ->
                     let mk_t t l uu___116_17481 =
                       match uu___116_17481 with
                       | [] -> t
                       | bs ->
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos in
                     let uu____17515 =
                       match_num_binders (bs1, (mk_t tbody1 lopt1))
                         (bs2, (mk_t tbody2 lopt2)) in
                     (match uu____17515 with
                      | ((bs11, tbody11), (bs21, tbody21)) ->
                          solve_binders env bs11 bs21 orig wl
                            (fun scope ->
                               fun env1 ->
                                 fun subst1 ->
                                   let uu____17651 =
                                     let uu____17656 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody11 in
                                     let uu____17657 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody21 in
                                     mk_problem scope orig uu____17656
                                       problem.FStar_TypeChecker_Common.relation
                                       uu____17657
                                       FStar_Pervasives_Native.None
                                       "lambda co-domain" in
                                   FStar_All.pipe_left
                                     (fun _0_67 ->
                                        FStar_TypeChecker_Common.TProb _0_67)
                                     uu____17651))
                 | (FStar_Syntax_Syntax.Tm_abs uu____17662, uu____17663) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____17688 -> true
                       | uu____17705 -> false in
                     let maybe_eta t =
                       if is_abs t
                       then FStar_Util.Inl t
                       else
                         (let t3 =
                            FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                          if is_abs t3
                          then FStar_Util.Inl t3
                          else FStar_Util.Inr t3) in
                     let force_eta t =
                       if is_abs t
                       then t
                       else
                         (let uu____17752 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___155_17760 = env in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___155_17760.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___155_17760.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___155_17760.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___155_17760.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___155_17760.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___155_17760.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___155_17760.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___155_17760.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___155_17760.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___155_17760.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___155_17760.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___155_17760.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___155_17760.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___155_17760.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___155_17760.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___155_17760.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___155_17760.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___155_17760.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___155_17760.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___155_17760.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___155_17760.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___155_17760.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___155_17760.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___155_17760.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___155_17760.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___155_17760.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___155_17760.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___155_17760.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___155_17760.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___155_17760.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___155_17760.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___155_17760.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___155_17760.FStar_TypeChecker_Env.dep_graph)
                               }) t in
                          match uu____17752 with
                          | (uu____17763, ty, uu____17765) ->
                              let uu____17766 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____17766) in
                     let uu____17767 =
                       let uu____17784 = maybe_eta t1 in
                       let uu____17791 = maybe_eta t2 in
                       (uu____17784, uu____17791) in
                     (match uu____17767 with
                      | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___156_17833 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___156_17833.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___156_17833.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___156_17833.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___156_17833.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___156_17833.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___156_17833.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___156_17833.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___156_17833.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                          let uu____17856 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                          if uu____17856
                          then
                            let uu____17857 =
                              destruct_flex_pattern env not_abs in
                            solve_t_flex_rigid true orig uu____17857 t_abs wl
                          else
                            (let t11 = force_eta t1 in
                             let t21 = force_eta t2 in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___157_17872 = problem in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___157_17872.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___157_17872.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___157_17872.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___157_17872.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___157_17872.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___157_17872.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___157_17872.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___157_17872.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                          let uu____17896 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                          if uu____17896
                          then
                            let uu____17897 =
                              destruct_flex_pattern env not_abs in
                            solve_t_flex_rigid true orig uu____17897 t_abs wl
                          else
                            (let t11 = force_eta t1 in
                             let t21 = force_eta t2 in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___157_17912 = problem in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___157_17912.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___157_17912.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___157_17912.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___157_17912.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___157_17912.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___157_17912.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___157_17912.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___157_17912.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____17916 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (uu____17933, FStar_Syntax_Syntax.Tm_abs uu____17934) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____17959 -> true
                       | uu____17976 -> false in
                     let maybe_eta t =
                       if is_abs t
                       then FStar_Util.Inl t
                       else
                         (let t3 =
                            FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                          if is_abs t3
                          then FStar_Util.Inl t3
                          else FStar_Util.Inr t3) in
                     let force_eta t =
                       if is_abs t
                       then t
                       else
                         (let uu____18023 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___155_18031 = env in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___155_18031.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___155_18031.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___155_18031.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___155_18031.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___155_18031.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___155_18031.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___155_18031.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___155_18031.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___155_18031.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___155_18031.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___155_18031.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___155_18031.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___155_18031.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___155_18031.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___155_18031.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___155_18031.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___155_18031.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___155_18031.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___155_18031.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___155_18031.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___155_18031.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___155_18031.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___155_18031.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___155_18031.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___155_18031.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___155_18031.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___155_18031.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___155_18031.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___155_18031.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___155_18031.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___155_18031.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___155_18031.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___155_18031.FStar_TypeChecker_Env.dep_graph)
                               }) t in
                          match uu____18023 with
                          | (uu____18034, ty, uu____18036) ->
                              let uu____18037 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____18037) in
                     let uu____18038 =
                       let uu____18055 = maybe_eta t1 in
                       let uu____18062 = maybe_eta t2 in
                       (uu____18055, uu____18062) in
                     (match uu____18038 with
                      | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___156_18104 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___156_18104.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___156_18104.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___156_18104.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___156_18104.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___156_18104.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___156_18104.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___156_18104.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___156_18104.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                          let uu____18127 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                          if uu____18127
                          then
                            let uu____18128 =
                              destruct_flex_pattern env not_abs in
                            solve_t_flex_rigid true orig uu____18128 t_abs wl
                          else
                            (let t11 = force_eta t1 in
                             let t21 = force_eta t2 in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___157_18143 = problem in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___157_18143.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___157_18143.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___157_18143.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___157_18143.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___157_18143.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___157_18143.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___157_18143.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___157_18143.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                          let uu____18167 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                          if uu____18167
                          then
                            let uu____18168 =
                              destruct_flex_pattern env not_abs in
                            solve_t_flex_rigid true orig uu____18168 t_abs wl
                          else
                            (let t11 = force_eta t1 in
                             let t21 = force_eta t2 in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___157_18183 = problem in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___157_18183.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___157_18183.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___157_18183.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___157_18183.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___157_18183.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___157_18183.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___157_18183.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___157_18183.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____18187 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (FStar_Syntax_Syntax.Tm_refine (x1, ph1),
                    FStar_Syntax_Syntax.Tm_refine (x2, phi2)) ->
                     let should_delta =
                       ((let uu____18219 = FStar_Syntax_Free.uvars t1 in
                         FStar_Util.set_is_empty uu____18219) &&
                          (let uu____18231 = FStar_Syntax_Free.uvars t2 in
                           FStar_Util.set_is_empty uu____18231))
                         &&
                         (let uu____18246 =
                            head_matches env x1.FStar_Syntax_Syntax.sort
                              x2.FStar_Syntax_Syntax.sort in
                          match uu____18246 with
                          | MisMatch
                              (FStar_Pervasives_Native.Some d1,
                               FStar_Pervasives_Native.Some d2)
                              ->
                              let is_unfoldable uu___117_18256 =
                                match uu___117_18256 with
                                | FStar_Syntax_Syntax.Delta_constant -> true
                                | FStar_Syntax_Syntax.Delta_defined_at_level
                                    uu____18257 -> true
                                | uu____18258 -> false in
                              (is_unfoldable d1) && (is_unfoldable d2)
                          | uu____18259 -> false) in
                     let uu____18260 = as_refinement should_delta env wl t1 in
                     (match uu____18260 with
                      | (x11, phi1) ->
                          let uu____18267 =
                            as_refinement should_delta env wl t2 in
                          (match uu____18267 with
                           | (x21, phi21) ->
                               let base_prob =
                                 let uu____18275 =
                                   let uu____18280 = p_scope orig in
                                   mk_problem uu____18280 orig
                                     x11.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.relation
                                     x21.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.element
                                     "refinement base type" in
                                 FStar_All.pipe_left
                                   (fun _0_68 ->
                                      FStar_TypeChecker_Common.TProb _0_68)
                                   uu____18275 in
                               let x12 = FStar_Syntax_Syntax.freshen_bv x11 in
                               let subst1 =
                                 [FStar_Syntax_Syntax.DB
                                    ((Prims.parse_int "0"), x12)] in
                               let phi11 =
                                 FStar_Syntax_Subst.subst subst1 phi1 in
                               let phi22 =
                                 FStar_Syntax_Subst.subst subst1 phi21 in
                               let env1 =
                                 FStar_TypeChecker_Env.push_bv env x12 in
                               let mk_imp1 imp phi12 phi23 =
                                 let uu____18314 = imp phi12 phi23 in
                                 FStar_All.pipe_right uu____18314
                                   (guard_on_element wl problem x12) in
                               let fallback uu____18318 =
                                 let impl =
                                   if
                                     problem.FStar_TypeChecker_Common.relation
                                       = FStar_TypeChecker_Common.EQ
                                   then
                                     mk_imp1 FStar_Syntax_Util.mk_iff phi11
                                       phi22
                                   else
                                     mk_imp1 FStar_Syntax_Util.mk_imp phi11
                                       phi22 in
                                 let guard =
                                   let uu____18324 =
                                     FStar_All.pipe_right (p_guard base_prob)
                                       FStar_Pervasives_Native.fst in
                                   FStar_Syntax_Util.mk_conj uu____18324 impl in
                                 let wl1 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl in
                                 solve env1 (attempt [base_prob] wl1) in
                               if
                                 problem.FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ
                               then
                                 let ref_prob =
                                   let uu____18333 =
                                     let uu____18338 =
                                       let uu____18339 = p_scope orig in
                                       let uu____18346 =
                                         let uu____18353 =
                                           FStar_Syntax_Syntax.mk_binder x12 in
                                         [uu____18353] in
                                       FStar_List.append uu____18339
                                         uu____18346 in
                                     mk_problem uu____18338 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula" in
                                   FStar_All.pipe_left
                                     (fun _0_69 ->
                                        FStar_TypeChecker_Common.TProb _0_69)
                                     uu____18333 in
                                 let uu____18362 =
                                   solve env1
                                     (let uu___158_18364 = wl in
                                      {
                                        attempting = [ref_prob];
                                        wl_deferred = [];
                                        ctr = (uu___158_18364.ctr);
                                        defer_ok = false;
                                        smt_ok = (uu___158_18364.smt_ok);
                                        tcenv = (uu___158_18364.tcenv)
                                      }) in
                                 (match uu____18362 with
                                  | Failed uu____18371 -> fallback ()
                                  | Success uu____18376 ->
                                      let guard =
                                        let uu____18380 =
                                          FStar_All.pipe_right
                                            (p_guard base_prob)
                                            FStar_Pervasives_Native.fst in
                                        let uu____18385 =
                                          let uu____18386 =
                                            FStar_All.pipe_right
                                              (p_guard ref_prob)
                                              FStar_Pervasives_Native.fst in
                                          FStar_All.pipe_right uu____18386
                                            (guard_on_element wl problem x12) in
                                        FStar_Syntax_Util.mk_conj uu____18380
                                          uu____18385 in
                                      let wl1 =
                                        solve_prob orig
                                          (FStar_Pervasives_Native.Some guard)
                                          [] wl in
                                      let wl2 =
                                        let uu___159_18395 = wl1 in
                                        {
                                          attempting =
                                            (uu___159_18395.attempting);
                                          wl_deferred =
                                            (uu___159_18395.wl_deferred);
                                          ctr =
                                            (wl1.ctr + (Prims.parse_int "1"));
                                          defer_ok =
                                            (uu___159_18395.defer_ok);
                                          smt_ok = (uu___159_18395.smt_ok);
                                          tcenv = (uu___159_18395.tcenv)
                                        } in
                                      solve env1 (attempt [base_prob] wl2))
                               else fallback ()))
                 | (FStar_Syntax_Syntax.Tm_uvar uu____18397,
                    FStar_Syntax_Syntax.Tm_uvar uu____18398) ->
                     let uu____18431 = destruct_flex_t t1 in
                     let uu____18432 = destruct_flex_t t2 in
                     flex_flex1 orig uu____18431 uu____18432
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18433;
                       FStar_Syntax_Syntax.pos = uu____18434;
                       FStar_Syntax_Syntax.vars = uu____18435;_},
                     uu____18436),
                    FStar_Syntax_Syntax.Tm_uvar uu____18437) ->
                     let uu____18490 = destruct_flex_t t1 in
                     let uu____18491 = destruct_flex_t t2 in
                     flex_flex1 orig uu____18490 uu____18491
                 | (FStar_Syntax_Syntax.Tm_uvar uu____18492,
                    FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18493;
                       FStar_Syntax_Syntax.pos = uu____18494;
                       FStar_Syntax_Syntax.vars = uu____18495;_},
                     uu____18496)) ->
                     let uu____18549 = destruct_flex_t t1 in
                     let uu____18550 = destruct_flex_t t2 in
                     flex_flex1 orig uu____18549 uu____18550
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18551;
                       FStar_Syntax_Syntax.pos = uu____18552;
                       FStar_Syntax_Syntax.vars = uu____18553;_},
                     uu____18554),
                    FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18555;
                       FStar_Syntax_Syntax.pos = uu____18556;
                       FStar_Syntax_Syntax.vars = uu____18557;_},
                     uu____18558)) ->
                     let uu____18631 = destruct_flex_t t1 in
                     let uu____18632 = destruct_flex_t t2 in
                     flex_flex1 orig uu____18631 uu____18632
                 | (FStar_Syntax_Syntax.Tm_uvar uu____18633, uu____18634)
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____18651 = destruct_flex_pattern env t1 in
                     solve_t_flex_rigid false orig uu____18651 t2 wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18658;
                       FStar_Syntax_Syntax.pos = uu____18659;
                       FStar_Syntax_Syntax.vars = uu____18660;_},
                     uu____18661),
                    uu____18662) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____18699 = destruct_flex_pattern env t1 in
                     solve_t_flex_rigid false orig uu____18699 t2 wl
                 | (uu____18706, FStar_Syntax_Syntax.Tm_uvar uu____18707)
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (uu____18724, FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18725;
                       FStar_Syntax_Syntax.pos = uu____18726;
                       FStar_Syntax_Syntax.vars = uu____18727;_},
                     uu____18728)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (FStar_Syntax_Syntax.Tm_uvar uu____18765,
                    FStar_Syntax_Syntax.Tm_type uu____18766) ->
                     solve_t' env
                       (let uu___160_18784 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___160_18784.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___160_18784.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___160_18784.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___160_18784.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___160_18784.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___160_18784.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___160_18784.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___160_18784.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___160_18784.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18785;
                       FStar_Syntax_Syntax.pos = uu____18786;
                       FStar_Syntax_Syntax.vars = uu____18787;_},
                     uu____18788),
                    FStar_Syntax_Syntax.Tm_type uu____18789) ->
                     solve_t' env
                       (let uu___160_18827 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___160_18827.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___160_18827.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___160_18827.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___160_18827.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___160_18827.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___160_18827.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___160_18827.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___160_18827.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___160_18827.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar uu____18828,
                    FStar_Syntax_Syntax.Tm_arrow uu____18829) ->
                     solve_t' env
                       (let uu___160_18859 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___160_18859.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___160_18859.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___160_18859.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___160_18859.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___160_18859.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___160_18859.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___160_18859.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___160_18859.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___160_18859.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18860;
                       FStar_Syntax_Syntax.pos = uu____18861;
                       FStar_Syntax_Syntax.vars = uu____18862;_},
                     uu____18863),
                    FStar_Syntax_Syntax.Tm_arrow uu____18864) ->
                     solve_t' env
                       (let uu___160_18914 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___160_18914.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___160_18914.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___160_18914.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___160_18914.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___160_18914.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___160_18914.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___160_18914.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___160_18914.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___160_18914.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar uu____18915, uu____18916) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation in
                        let uu____18935 =
                          let uu____18936 = is_top_level_prob orig in
                          FStar_All.pipe_left Prims.op_Negation uu____18936 in
                        if uu____18935
                        then
                          let uu____18937 =
                            FStar_All.pipe_left
                              (fun _0_70 ->
                                 FStar_TypeChecker_Common.TProb _0_70)
                              (let uu___161_18943 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___161_18943.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___161_18943.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___161_18943.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___161_18943.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___161_18943.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___161_18943.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___161_18943.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___161_18943.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___161_18943.FStar_TypeChecker_Common.rank)
                               }) in
                          let uu____18944 = destruct_flex_pattern env t1 in
                          solve_t_flex_rigid false uu____18937 uu____18944 t2
                            wl
                        else
                          (let uu____18952 = base_and_refinement env t2 in
                           match uu____18952 with
                           | (t_base, ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None ->
                                    let uu____18981 =
                                      FStar_All.pipe_left
                                        (fun _0_71 ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_71)
                                        (let uu___162_18987 = problem in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___162_18987.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___162_18987.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___162_18987.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___162_18987.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___162_18987.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___162_18987.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___162_18987.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___162_18987.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___162_18987.FStar_TypeChecker_Common.rank)
                                         }) in
                                    let uu____18988 =
                                      destruct_flex_pattern env t1 in
                                    solve_t_flex_rigid false uu____18981
                                      uu____18988 t_base wl
                                | FStar_Pervasives_Native.Some (y, phi) ->
                                    let y' =
                                      let uu___163_19002 = y in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___163_19002.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___163_19002.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      } in
                                    let impl =
                                      guard_on_element wl problem y' phi in
                                    let base_prob =
                                      let uu____19005 =
                                        mk_problem
                                          problem.FStar_TypeChecker_Common.scope
                                          orig t1 new_rel
                                          y.FStar_Syntax_Syntax.sort
                                          problem.FStar_TypeChecker_Common.element
                                          "flex-rigid: base type" in
                                      FStar_All.pipe_left
                                        (fun _0_72 ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_72) uu____19005 in
                                    let guard =
                                      let uu____19017 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      FStar_Syntax_Util.mk_conj uu____19017
                                        impl in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    solve env (attempt [base_prob] wl1))))
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19025;
                       FStar_Syntax_Syntax.pos = uu____19026;
                       FStar_Syntax_Syntax.vars = uu____19027;_},
                     uu____19028),
                    uu____19029) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation in
                        let uu____19068 =
                          let uu____19069 = is_top_level_prob orig in
                          FStar_All.pipe_left Prims.op_Negation uu____19069 in
                        if uu____19068
                        then
                          let uu____19070 =
                            FStar_All.pipe_left
                              (fun _0_73 ->
                                 FStar_TypeChecker_Common.TProb _0_73)
                              (let uu___161_19076 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___161_19076.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___161_19076.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___161_19076.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___161_19076.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___161_19076.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___161_19076.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___161_19076.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___161_19076.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___161_19076.FStar_TypeChecker_Common.rank)
                               }) in
                          let uu____19077 = destruct_flex_pattern env t1 in
                          solve_t_flex_rigid false uu____19070 uu____19077 t2
                            wl
                        else
                          (let uu____19085 = base_and_refinement env t2 in
                           match uu____19085 with
                           | (t_base, ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None ->
                                    let uu____19114 =
                                      FStar_All.pipe_left
                                        (fun _0_74 ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_74)
                                        (let uu___162_19120 = problem in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___162_19120.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___162_19120.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___162_19120.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___162_19120.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___162_19120.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___162_19120.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___162_19120.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___162_19120.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___162_19120.FStar_TypeChecker_Common.rank)
                                         }) in
                                    let uu____19121 =
                                      destruct_flex_pattern env t1 in
                                    solve_t_flex_rigid false uu____19114
                                      uu____19121 t_base wl
                                | FStar_Pervasives_Native.Some (y, phi) ->
                                    let y' =
                                      let uu___163_19135 = y in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___163_19135.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___163_19135.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      } in
                                    let impl =
                                      guard_on_element wl problem y' phi in
                                    let base_prob =
                                      let uu____19138 =
                                        mk_problem
                                          problem.FStar_TypeChecker_Common.scope
                                          orig t1 new_rel
                                          y.FStar_Syntax_Syntax.sort
                                          problem.FStar_TypeChecker_Common.element
                                          "flex-rigid: base type" in
                                      FStar_All.pipe_left
                                        (fun _0_75 ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_75) uu____19138 in
                                    let guard =
                                      let uu____19150 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      FStar_Syntax_Util.mk_conj uu____19150
                                        impl in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    solve env (attempt [base_prob] wl1))))
                 | (uu____19158, FStar_Syntax_Syntax.Tm_uvar uu____19159) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____19177 = base_and_refinement env t1 in
                        match uu____19177 with
                        | (t_base, uu____19189) ->
                            solve_t env
                              (let uu___164_19203 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___164_19203.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___164_19203.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___164_19203.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___164_19203.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___164_19203.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___164_19203.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___164_19203.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___164_19203.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (uu____19204, FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19205;
                       FStar_Syntax_Syntax.pos = uu____19206;
                       FStar_Syntax_Syntax.vars = uu____19207;_},
                     uu____19208)) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____19246 = base_and_refinement env t1 in
                        match uu____19246 with
                        | (t_base, uu____19258) ->
                            solve_t env
                              (let uu___164_19272 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___164_19272.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___164_19272.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___164_19272.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___164_19272.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___164_19272.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___164_19272.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___164_19272.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___164_19272.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_fvar fv;
                            FStar_Syntax_Syntax.pos = uu____19274;
                            FStar_Syntax_Syntax.vars = uu____19275;_},
                          uu____19276);
                       FStar_Syntax_Syntax.pos = uu____19277;
                       FStar_Syntax_Syntax.vars = uu____19278;_},
                     uu____19279),
                    uu____19280) when
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.t_refine_lid)
                       ||
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.p_refine_lid)
                     ->
                     let t11 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Eager_unfolding] env t1 in
                     solve_t env
                       (let uu___165_19307 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___165_19307.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___165_19307.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs =
                            (uu___165_19307.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___165_19307.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___165_19307.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___165_19307.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___165_19307.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___165_19307.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___165_19307.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____19309;
                       FStar_Syntax_Syntax.vars = uu____19310;_},
                     uu____19311),
                    uu____19312) when
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.t_refine_lid)
                       ||
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.p_refine_lid)
                     ->
                     let t11 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Eager_unfolding] env t1 in
                     solve_t env
                       (let uu___165_19335 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___165_19335.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___165_19335.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs =
                            (uu___165_19335.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___165_19335.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___165_19335.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___165_19335.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___165_19335.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___165_19335.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___165_19335.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (uu____19336, FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_fvar fv;
                            FStar_Syntax_Syntax.pos = uu____19338;
                            FStar_Syntax_Syntax.vars = uu____19339;_},
                          uu____19340);
                       FStar_Syntax_Syntax.pos = uu____19341;
                       FStar_Syntax_Syntax.vars = uu____19342;_},
                     uu____19343)) when
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.t_refine_lid)
                       ||
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.p_refine_lid)
                     ->
                     let t21 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Eager_unfolding] env t2 in
                     solve_t env
                       (let uu___166_19370 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___166_19370.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___166_19370.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            (uu___166_19370.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___166_19370.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___166_19370.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___166_19370.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___166_19370.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___166_19370.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___166_19370.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (uu____19371, FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____19373;
                       FStar_Syntax_Syntax.vars = uu____19374;_},
                     uu____19375)) when
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.t_refine_lid)
                       ||
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.p_refine_lid)
                     ->
                     let t21 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Eager_unfolding] env t2 in
                     solve_t env
                       (let uu___166_19398 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___166_19398.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___166_19398.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            (uu___166_19398.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___166_19398.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___166_19398.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___166_19398.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___166_19398.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___166_19398.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___166_19398.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_refine uu____19399, uu____19400)
                     ->
                     let t21 =
                       let uu____19410 = base_and_refinement env t2 in
                       FStar_All.pipe_left force_refinement uu____19410 in
                     solve_t env
                       (let uu___167_19434 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___167_19434.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___167_19434.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            (uu___167_19434.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___167_19434.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___167_19434.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___167_19434.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___167_19434.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___167_19434.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___167_19434.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (uu____19435, FStar_Syntax_Syntax.Tm_refine uu____19436)
                     ->
                     let t11 =
                       let uu____19446 = base_and_refinement env t1 in
                       FStar_All.pipe_left force_refinement uu____19446 in
                     solve_t env
                       (let uu___168_19470 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___168_19470.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___168_19470.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs =
                            (uu___168_19470.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___168_19470.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___168_19470.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___168_19470.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___168_19470.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___168_19470.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___168_19470.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_match uu____19473, uu____19474) ->
                     let head1 =
                       let uu____19500 = FStar_Syntax_Util.head_and_args t1 in
                       FStar_All.pipe_right uu____19500
                         FStar_Pervasives_Native.fst in
                     let head2 =
                       let uu____19544 = FStar_Syntax_Util.head_and_args t2 in
                       FStar_All.pipe_right uu____19544
                         FStar_Pervasives_Native.fst in
                     ((let uu____19586 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck") in
                       if uu____19586
                       then
                         let uu____19587 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid in
                         let uu____19588 =
                           FStar_Syntax_Print.term_to_string head1 in
                         let uu____19589 =
                           FStar_Syntax_Print.term_to_string head2 in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____19587 uu____19588 uu____19589
                       else ());
                      (let uu____19591 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ) in
                       if uu____19591
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1 in
                         let uv2 = FStar_Syntax_Free.uvars t2 in
                         let uu____19606 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2) in
                         (if uu____19606
                          then
                            let guard =
                              let uu____19618 =
                                let uu____19619 =
                                  FStar_Syntax_Util.eq_tm t1 t2 in
                                uu____19619 = FStar_Syntax_Util.Equal in
                              if uu____19618
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____19623 = mk_eq2 orig t1 t2 in
                                 FStar_All.pipe_left
                                   (fun _0_76 ->
                                      FStar_Pervasives_Native.Some _0_76)
                                   uu____19623) in
                            let uu____19626 = solve_prob orig guard [] wl in
                            solve env uu____19626
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_uinst uu____19629, uu____19630) ->
                     let head1 =
                       let uu____19640 = FStar_Syntax_Util.head_and_args t1 in
                       FStar_All.pipe_right uu____19640
                         FStar_Pervasives_Native.fst in
                     let head2 =
                       let uu____19684 = FStar_Syntax_Util.head_and_args t2 in
                       FStar_All.pipe_right uu____19684
                         FStar_Pervasives_Native.fst in
                     ((let uu____19726 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck") in
                       if uu____19726
                       then
                         let uu____19727 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid in
                         let uu____19728 =
                           FStar_Syntax_Print.term_to_string head1 in
                         let uu____19729 =
                           FStar_Syntax_Print.term_to_string head2 in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____19727 uu____19728 uu____19729
                       else ());
                      (let uu____19731 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ) in
                       if uu____19731
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1 in
                         let uv2 = FStar_Syntax_Free.uvars t2 in
                         let uu____19746 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2) in
                         (if uu____19746
                          then
                            let guard =
                              let uu____19758 =
                                let uu____19759 =
                                  FStar_Syntax_Util.eq_tm t1 t2 in
                                uu____19759 = FStar_Syntax_Util.Equal in
                              if uu____19758
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____19763 = mk_eq2 orig t1 t2 in
                                 FStar_All.pipe_left
                                   (fun _0_77 ->
                                      FStar_Pervasives_Native.Some _0_77)
                                   uu____19763) in
                            let uu____19766 = solve_prob orig guard [] wl in
                            solve env uu____19766
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_name uu____19769, uu____19770) ->
                     let head1 =
                       let uu____19774 = FStar_Syntax_Util.head_and_args t1 in
                       FStar_All.pipe_right uu____19774
                         FStar_Pervasives_Native.fst in
                     let head2 =
                       let uu____19818 = FStar_Syntax_Util.head_and_args t2 in
                       FStar_All.pipe_right uu____19818
                         FStar_Pervasives_Native.fst in
                     ((let uu____19860 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck") in
                       if uu____19860
                       then
                         let uu____19861 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid in
                         let uu____19862 =
                           FStar_Syntax_Print.term_to_string head1 in
                         let uu____19863 =
                           FStar_Syntax_Print.term_to_string head2 in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____19861 uu____19862 uu____19863
                       else ());
                      (let uu____19865 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ) in
                       if uu____19865
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1 in
                         let uv2 = FStar_Syntax_Free.uvars t2 in
                         let uu____19880 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2) in
                         (if uu____19880
                          then
                            let guard =
                              let uu____19892 =
                                let uu____19893 =
                                  FStar_Syntax_Util.eq_tm t1 t2 in
                                uu____19893 = FStar_Syntax_Util.Equal in
                              if uu____19892
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____19897 = mk_eq2 orig t1 t2 in
                                 FStar_All.pipe_left
                                   (fun _0_78 ->
                                      FStar_Pervasives_Native.Some _0_78)
                                   uu____19897) in
                            let uu____19900 = solve_prob orig guard [] wl in
                            solve env uu____19900
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_constant uu____19903, uu____19904)
                     ->
                     let head1 =
                       let uu____19908 = FStar_Syntax_Util.head_and_args t1 in
                       FStar_All.pipe_right uu____19908
                         FStar_Pervasives_Native.fst in
                     let head2 =
                       let uu____19952 = FStar_Syntax_Util.head_and_args t2 in
                       FStar_All.pipe_right uu____19952
                         FStar_Pervasives_Native.fst in
                     ((let uu____19994 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck") in
                       if uu____19994
                       then
                         let uu____19995 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid in
                         let uu____19996 =
                           FStar_Syntax_Print.term_to_string head1 in
                         let uu____19997 =
                           FStar_Syntax_Print.term_to_string head2 in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____19995 uu____19996 uu____19997
                       else ());
                      (let uu____19999 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ) in
                       if uu____19999
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1 in
                         let uv2 = FStar_Syntax_Free.uvars t2 in
                         let uu____20014 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2) in
                         (if uu____20014
                          then
                            let guard =
                              let uu____20026 =
                                let uu____20027 =
                                  FStar_Syntax_Util.eq_tm t1 t2 in
                                uu____20027 = FStar_Syntax_Util.Equal in
                              if uu____20026
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20031 = mk_eq2 orig t1 t2 in
                                 FStar_All.pipe_left
                                   (fun _0_79 ->
                                      FStar_Pervasives_Native.Some _0_79)
                                   uu____20031) in
                            let uu____20034 = solve_prob orig guard [] wl in
                            solve env uu____20034
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_fvar uu____20037, uu____20038) ->
                     let head1 =
                       let uu____20042 = FStar_Syntax_Util.head_and_args t1 in
                       FStar_All.pipe_right uu____20042
                         FStar_Pervasives_Native.fst in
                     let head2 =
                       let uu____20086 = FStar_Syntax_Util.head_and_args t2 in
                       FStar_All.pipe_right uu____20086
                         FStar_Pervasives_Native.fst in
                     ((let uu____20128 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck") in
                       if uu____20128
                       then
                         let uu____20129 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid in
                         let uu____20130 =
                           FStar_Syntax_Print.term_to_string head1 in
                         let uu____20131 =
                           FStar_Syntax_Print.term_to_string head2 in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20129 uu____20130 uu____20131
                       else ());
                      (let uu____20133 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ) in
                       if uu____20133
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1 in
                         let uv2 = FStar_Syntax_Free.uvars t2 in
                         let uu____20148 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2) in
                         (if uu____20148
                          then
                            let guard =
                              let uu____20160 =
                                let uu____20161 =
                                  FStar_Syntax_Util.eq_tm t1 t2 in
                                uu____20161 = FStar_Syntax_Util.Equal in
                              if uu____20160
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20165 = mk_eq2 orig t1 t2 in
                                 FStar_All.pipe_left
                                   (fun _0_80 ->
                                      FStar_Pervasives_Native.Some _0_80)
                                   uu____20165) in
                            let uu____20168 = solve_prob orig guard [] wl in
                            solve env uu____20168
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_app uu____20171, uu____20172) ->
                     let head1 =
                       let uu____20190 = FStar_Syntax_Util.head_and_args t1 in
                       FStar_All.pipe_right uu____20190
                         FStar_Pervasives_Native.fst in
                     let head2 =
                       let uu____20234 = FStar_Syntax_Util.head_and_args t2 in
                       FStar_All.pipe_right uu____20234
                         FStar_Pervasives_Native.fst in
                     ((let uu____20276 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck") in
                       if uu____20276
                       then
                         let uu____20277 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid in
                         let uu____20278 =
                           FStar_Syntax_Print.term_to_string head1 in
                         let uu____20279 =
                           FStar_Syntax_Print.term_to_string head2 in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20277 uu____20278 uu____20279
                       else ());
                      (let uu____20281 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ) in
                       if uu____20281
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1 in
                         let uv2 = FStar_Syntax_Free.uvars t2 in
                         let uu____20296 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2) in
                         (if uu____20296
                          then
                            let guard =
                              let uu____20308 =
                                let uu____20309 =
                                  FStar_Syntax_Util.eq_tm t1 t2 in
                                uu____20309 = FStar_Syntax_Util.Equal in
                              if uu____20308
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20313 = mk_eq2 orig t1 t2 in
                                 FStar_All.pipe_left
                                   (fun _0_81 ->
                                      FStar_Pervasives_Native.Some _0_81)
                                   uu____20313) in
                            let uu____20316 = solve_prob orig guard [] wl in
                            solve env uu____20316
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20319, FStar_Syntax_Syntax.Tm_match uu____20320) ->
                     let head1 =
                       let uu____20346 = FStar_Syntax_Util.head_and_args t1 in
                       FStar_All.pipe_right uu____20346
                         FStar_Pervasives_Native.fst in
                     let head2 =
                       let uu____20390 = FStar_Syntax_Util.head_and_args t2 in
                       FStar_All.pipe_right uu____20390
                         FStar_Pervasives_Native.fst in
                     ((let uu____20432 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck") in
                       if uu____20432
                       then
                         let uu____20433 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid in
                         let uu____20434 =
                           FStar_Syntax_Print.term_to_string head1 in
                         let uu____20435 =
                           FStar_Syntax_Print.term_to_string head2 in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20433 uu____20434 uu____20435
                       else ());
                      (let uu____20437 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ) in
                       if uu____20437
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1 in
                         let uv2 = FStar_Syntax_Free.uvars t2 in
                         let uu____20452 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2) in
                         (if uu____20452
                          then
                            let guard =
                              let uu____20464 =
                                let uu____20465 =
                                  FStar_Syntax_Util.eq_tm t1 t2 in
                                uu____20465 = FStar_Syntax_Util.Equal in
                              if uu____20464
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20469 = mk_eq2 orig t1 t2 in
                                 FStar_All.pipe_left
                                   (fun _0_82 ->
                                      FStar_Pervasives_Native.Some _0_82)
                                   uu____20469) in
                            let uu____20472 = solve_prob orig guard [] wl in
                            solve env uu____20472
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20475, FStar_Syntax_Syntax.Tm_uinst uu____20476) ->
                     let head1 =
                       let uu____20486 = FStar_Syntax_Util.head_and_args t1 in
                       FStar_All.pipe_right uu____20486
                         FStar_Pervasives_Native.fst in
                     let head2 =
                       let uu____20530 = FStar_Syntax_Util.head_and_args t2 in
                       FStar_All.pipe_right uu____20530
                         FStar_Pervasives_Native.fst in
                     ((let uu____20572 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck") in
                       if uu____20572
                       then
                         let uu____20573 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid in
                         let uu____20574 =
                           FStar_Syntax_Print.term_to_string head1 in
                         let uu____20575 =
                           FStar_Syntax_Print.term_to_string head2 in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20573 uu____20574 uu____20575
                       else ());
                      (let uu____20577 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ) in
                       if uu____20577
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1 in
                         let uv2 = FStar_Syntax_Free.uvars t2 in
                         let uu____20592 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2) in
                         (if uu____20592
                          then
                            let guard =
                              let uu____20604 =
                                let uu____20605 =
                                  FStar_Syntax_Util.eq_tm t1 t2 in
                                uu____20605 = FStar_Syntax_Util.Equal in
                              if uu____20604
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20609 = mk_eq2 orig t1 t2 in
                                 FStar_All.pipe_left
                                   (fun _0_83 ->
                                      FStar_Pervasives_Native.Some _0_83)
                                   uu____20609) in
                            let uu____20612 = solve_prob orig guard [] wl in
                            solve env uu____20612
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20615, FStar_Syntax_Syntax.Tm_name uu____20616) ->
                     let head1 =
                       let uu____20620 = FStar_Syntax_Util.head_and_args t1 in
                       FStar_All.pipe_right uu____20620
                         FStar_Pervasives_Native.fst in
                     let head2 =
                       let uu____20664 = FStar_Syntax_Util.head_and_args t2 in
                       FStar_All.pipe_right uu____20664
                         FStar_Pervasives_Native.fst in
                     ((let uu____20706 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck") in
                       if uu____20706
                       then
                         let uu____20707 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid in
                         let uu____20708 =
                           FStar_Syntax_Print.term_to_string head1 in
                         let uu____20709 =
                           FStar_Syntax_Print.term_to_string head2 in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20707 uu____20708 uu____20709
                       else ());
                      (let uu____20711 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ) in
                       if uu____20711
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1 in
                         let uv2 = FStar_Syntax_Free.uvars t2 in
                         let uu____20726 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2) in
                         (if uu____20726
                          then
                            let guard =
                              let uu____20738 =
                                let uu____20739 =
                                  FStar_Syntax_Util.eq_tm t1 t2 in
                                uu____20739 = FStar_Syntax_Util.Equal in
                              if uu____20738
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20743 = mk_eq2 orig t1 t2 in
                                 FStar_All.pipe_left
                                   (fun _0_84 ->
                                      FStar_Pervasives_Native.Some _0_84)
                                   uu____20743) in
                            let uu____20746 = solve_prob orig guard [] wl in
                            solve env uu____20746
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20749, FStar_Syntax_Syntax.Tm_constant uu____20750)
                     ->
                     let head1 =
                       let uu____20754 = FStar_Syntax_Util.head_and_args t1 in
                       FStar_All.pipe_right uu____20754
                         FStar_Pervasives_Native.fst in
                     let head2 =
                       let uu____20798 = FStar_Syntax_Util.head_and_args t2 in
                       FStar_All.pipe_right uu____20798
                         FStar_Pervasives_Native.fst in
                     ((let uu____20840 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck") in
                       if uu____20840
                       then
                         let uu____20841 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid in
                         let uu____20842 =
                           FStar_Syntax_Print.term_to_string head1 in
                         let uu____20843 =
                           FStar_Syntax_Print.term_to_string head2 in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20841 uu____20842 uu____20843
                       else ());
                      (let uu____20845 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ) in
                       if uu____20845
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1 in
                         let uv2 = FStar_Syntax_Free.uvars t2 in
                         let uu____20860 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2) in
                         (if uu____20860
                          then
                            let guard =
                              let uu____20872 =
                                let uu____20873 =
                                  FStar_Syntax_Util.eq_tm t1 t2 in
                                uu____20873 = FStar_Syntax_Util.Equal in
                              if uu____20872
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20877 = mk_eq2 orig t1 t2 in
                                 FStar_All.pipe_left
                                   (fun _0_85 ->
                                      FStar_Pervasives_Native.Some _0_85)
                                   uu____20877) in
                            let uu____20880 = solve_prob orig guard [] wl in
                            solve env uu____20880
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20883, FStar_Syntax_Syntax.Tm_fvar uu____20884) ->
                     let head1 =
                       let uu____20888 = FStar_Syntax_Util.head_and_args t1 in
                       FStar_All.pipe_right uu____20888
                         FStar_Pervasives_Native.fst in
                     let head2 =
                       let uu____20932 = FStar_Syntax_Util.head_and_args t2 in
                       FStar_All.pipe_right uu____20932
                         FStar_Pervasives_Native.fst in
                     ((let uu____20974 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck") in
                       if uu____20974
                       then
                         let uu____20975 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid in
                         let uu____20976 =
                           FStar_Syntax_Print.term_to_string head1 in
                         let uu____20977 =
                           FStar_Syntax_Print.term_to_string head2 in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20975 uu____20976 uu____20977
                       else ());
                      (let uu____20979 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ) in
                       if uu____20979
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1 in
                         let uv2 = FStar_Syntax_Free.uvars t2 in
                         let uu____20994 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2) in
                         (if uu____20994
                          then
                            let guard =
                              let uu____21006 =
                                let uu____21007 =
                                  FStar_Syntax_Util.eq_tm t1 t2 in
                                uu____21007 = FStar_Syntax_Util.Equal in
                              if uu____21006
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21011 = mk_eq2 orig t1 t2 in
                                 FStar_All.pipe_left
                                   (fun _0_86 ->
                                      FStar_Pervasives_Native.Some _0_86)
                                   uu____21011) in
                            let uu____21014 = solve_prob orig guard [] wl in
                            solve env uu____21014
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____21017, FStar_Syntax_Syntax.Tm_app uu____21018) ->
                     let head1 =
                       let uu____21036 = FStar_Syntax_Util.head_and_args t1 in
                       FStar_All.pipe_right uu____21036
                         FStar_Pervasives_Native.fst in
                     let head2 =
                       let uu____21080 = FStar_Syntax_Util.head_and_args t2 in
                       FStar_All.pipe_right uu____21080
                         FStar_Pervasives_Native.fst in
                     ((let uu____21122 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck") in
                       if uu____21122
                       then
                         let uu____21123 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid in
                         let uu____21124 =
                           FStar_Syntax_Print.term_to_string head1 in
                         let uu____21125 =
                           FStar_Syntax_Print.term_to_string head2 in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21123 uu____21124 uu____21125
                       else ());
                      (let uu____21127 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ) in
                       if uu____21127
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1 in
                         let uv2 = FStar_Syntax_Free.uvars t2 in
                         let uu____21142 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2) in
                         (if uu____21142
                          then
                            let guard =
                              let uu____21154 =
                                let uu____21155 =
                                  FStar_Syntax_Util.eq_tm t1 t2 in
                                uu____21155 = FStar_Syntax_Util.Equal in
                              if uu____21154
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21159 = mk_eq2 orig t1 t2 in
                                 FStar_All.pipe_left
                                   (fun _0_87 ->
                                      FStar_Pervasives_Native.Some _0_87)
                                   uu____21159) in
                            let uu____21162 = solve_prob orig guard [] wl in
                            solve env uu____21162
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_let uu____21165,
                    FStar_Syntax_Syntax.Tm_let uu____21166) ->
                     let uu____21191 = FStar_Syntax_Util.term_eq t1 t2 in
                     if uu____21191
                     then
                       let uu____21192 =
                         solve_prob orig FStar_Pervasives_Native.None [] wl in
                       solve env uu____21192
                     else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
                 | (FStar_Syntax_Syntax.Tm_let uu____21194, uu____21195) ->
                     let uu____21208 =
                       let uu____21213 =
                         let uu____21214 = FStar_Syntax_Print.tag_of_term t1 in
                         let uu____21215 = FStar_Syntax_Print.tag_of_term t2 in
                         let uu____21216 =
                           FStar_Syntax_Print.term_to_string t1 in
                         let uu____21217 =
                           FStar_Syntax_Print.term_to_string t2 in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____21214 uu____21215 uu____21216 uu____21217 in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____21213) in
                     FStar_Errors.raise_error uu____21208
                       t1.FStar_Syntax_Syntax.pos
                 | (uu____21218, FStar_Syntax_Syntax.Tm_let uu____21219) ->
                     let uu____21232 =
                       let uu____21237 =
                         let uu____21238 = FStar_Syntax_Print.tag_of_term t1 in
                         let uu____21239 = FStar_Syntax_Print.tag_of_term t2 in
                         let uu____21240 =
                           FStar_Syntax_Print.term_to_string t1 in
                         let uu____21241 =
                           FStar_Syntax_Print.term_to_string t2 in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____21238 uu____21239 uu____21240 uu____21241 in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____21237) in
                     FStar_Errors.raise_error uu____21232
                       t1.FStar_Syntax_Syntax.pos
                 | uu____21242 -> giveup env "head tag mismatch" orig)))))
and (solve_c :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem
      -> worklist -> solution)
  =
  fun env ->
    fun problem ->
      fun wl ->
        let c1 = problem.FStar_TypeChecker_Common.lhs in
        let c2 = problem.FStar_TypeChecker_Common.rhs in
        let orig = FStar_TypeChecker_Common.CProb problem in
        let sub_prob t1 rel t2 reason =
          let uu____21270 = p_scope orig in
          mk_problem uu____21270 orig t1 rel t2 FStar_Pervasives_Native.None
            reason in
        let solve_eq c1_comp c2_comp =
          (let uu____21279 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____21279
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____21281 =
               let uu____21282 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____21283 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____21282 uu____21283 in
             giveup env uu____21281 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____21303 ->
                    fun uu____21304 ->
                      match (uu____21303, uu____21304) with
                      | ((a1, uu____21322), (a2, uu____21324)) ->
                          let uu____21333 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_88 ->
                               FStar_TypeChecker_Common.TProb _0_88)
                            uu____21333)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____21343 =
                 FStar_List.map
                   (fun p ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____21343 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____21367 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1, uu____21374)::[] -> wp1
              | uu____21391 ->
                  let uu____21400 =
                    let uu____21401 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____21401 in
                  failwith uu____21400 in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____21409 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ in
                  [uu____21409]
              | x -> x in
            let uu____21411 =
              let uu____21420 =
                let uu____21421 =
                  let uu____21422 = FStar_List.hd univs1 in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____21422 c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____21421 in
              [uu____21420] in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____21411;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____21423 = lift_c1 () in solve_eq uu____21423 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___118_21429 ->
                       match uu___118_21429 with
                       | FStar_Syntax_Syntax.TOTAL -> true
                       | FStar_Syntax_Syntax.MLEFFECT -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL -> true
                       | uu____21430 -> false)) in
             let uu____21431 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1, uu____21465)::uu____21466,
                  (wp2, uu____21468)::uu____21469) -> (wp1, wp2)
               | uu____21526 ->
                   let uu____21547 =
                     let uu____21552 =
                       let uu____21553 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name in
                       let uu____21554 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____21553 uu____21554 in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____21552) in
                   FStar_Errors.raise_error uu____21547
                     env.FStar_TypeChecker_Env.range in
             match uu____21431 with
             | (wpc1, wpc2) ->
                 let uu____21573 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____21573
                 then
                   let uu____21576 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____21576 wl
                 else
                   (let uu____21580 =
                      let uu____21587 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____21587 in
                    match uu____21580 with
                    | (c2_decl, qualifiers) ->
                        let uu____21608 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____21608
                        then
                          let c1_repr =
                            let uu____21612 =
                              let uu____21613 =
                                let uu____21614 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____21614 in
                              let uu____21615 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21613 uu____21615 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21612 in
                          let c2_repr =
                            let uu____21617 =
                              let uu____21618 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____21619 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21618 uu____21619 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21617 in
                          let prob =
                            let uu____21621 =
                              let uu____21626 =
                                let uu____21627 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____21628 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____21627
                                  uu____21628 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____21626 in
                            FStar_TypeChecker_Common.TProb uu____21621 in
                          let wl1 =
                            let uu____21630 =
                              let uu____21633 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____21633 in
                            solve_prob orig uu____21630 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____21642 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____21642
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ in
                                   let uu____21645 =
                                     let uu____21648 =
                                       let uu____21649 =
                                         let uu____21664 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____21665 =
                                           let uu____21668 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____21669 =
                                             let uu____21672 =
                                               let uu____21673 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____21673 in
                                             [uu____21672] in
                                           uu____21668 :: uu____21669 in
                                         (uu____21664, uu____21665) in
                                       FStar_Syntax_Syntax.Tm_app uu____21649 in
                                     FStar_Syntax_Syntax.mk uu____21648 in
                                   uu____21645 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ in
                                  let uu____21682 =
                                    let uu____21685 =
                                      let uu____21686 =
                                        let uu____21701 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____21702 =
                                          let uu____21705 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____21706 =
                                            let uu____21709 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____21710 =
                                              let uu____21713 =
                                                let uu____21714 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21714 in
                                              [uu____21713] in
                                            uu____21709 :: uu____21710 in
                                          uu____21705 :: uu____21706 in
                                        (uu____21701, uu____21702) in
                                      FStar_Syntax_Syntax.Tm_app uu____21686 in
                                    FStar_Syntax_Syntax.mk uu____21685 in
                                  uu____21682 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____21721 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_89 ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____21721 in
                           let wl1 =
                             let uu____21731 =
                               let uu____21734 =
                                 let uu____21737 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____21737 g in
                               FStar_All.pipe_left
                                 (fun _0_90 ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____21734 in
                             solve_prob orig uu____21731 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____21750 = FStar_Util.physical_equality c1 c2 in
        if uu____21750
        then
          let uu____21751 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____21751
        else
          ((let uu____21754 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____21754
            then
              let uu____21755 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____21756 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21755
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21756
            else ());
           (let uu____21758 =
              let uu____21763 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____21764 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____21763, uu____21764) in
            match uu____21758 with
            | (c11, c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____21768),
                    FStar_Syntax_Syntax.Total (t2, uu____21770)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21787 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21787 wl
                 | (FStar_Syntax_Syntax.GTotal uu____21790,
                    FStar_Syntax_Syntax.Total uu____21791) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total (t1, uu____21809),
                    FStar_Syntax_Syntax.Total (t2, uu____21811)) ->
                     let uu____21828 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21828 wl
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____21832),
                    FStar_Syntax_Syntax.GTotal (t2, uu____21834)) ->
                     let uu____21851 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21851 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____21855),
                    FStar_Syntax_Syntax.GTotal (t2, uu____21857)) ->
                     let uu____21874 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21874 wl
                 | (FStar_Syntax_Syntax.GTotal uu____21877,
                    FStar_Syntax_Syntax.Comp uu____21878) ->
                     let uu____21887 =
                       let uu___169_21892 = problem in
                       let uu____21897 =
                         let uu____21898 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21898 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___169_21892.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21897;
                         FStar_TypeChecker_Common.relation =
                           (uu___169_21892.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___169_21892.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___169_21892.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___169_21892.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___169_21892.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___169_21892.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___169_21892.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___169_21892.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21887 wl
                 | (FStar_Syntax_Syntax.Total uu____21899,
                    FStar_Syntax_Syntax.Comp uu____21900) ->
                     let uu____21909 =
                       let uu___169_21914 = problem in
                       let uu____21919 =
                         let uu____21920 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21920 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___169_21914.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21919;
                         FStar_TypeChecker_Common.relation =
                           (uu___169_21914.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___169_21914.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___169_21914.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___169_21914.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___169_21914.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___169_21914.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___169_21914.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___169_21914.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21909 wl
                 | (FStar_Syntax_Syntax.Comp uu____21921,
                    FStar_Syntax_Syntax.GTotal uu____21922) ->
                     let uu____21931 =
                       let uu___170_21936 = problem in
                       let uu____21941 =
                         let uu____21942 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21942 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___170_21936.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___170_21936.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___170_21936.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21941;
                         FStar_TypeChecker_Common.element =
                           (uu___170_21936.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___170_21936.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___170_21936.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___170_21936.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___170_21936.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___170_21936.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21931 wl
                 | (FStar_Syntax_Syntax.Comp uu____21943,
                    FStar_Syntax_Syntax.Total uu____21944) ->
                     let uu____21953 =
                       let uu___170_21958 = problem in
                       let uu____21963 =
                         let uu____21964 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21964 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___170_21958.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___170_21958.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___170_21958.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21963;
                         FStar_TypeChecker_Common.element =
                           (uu___170_21958.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___170_21958.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___170_21958.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___170_21958.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___170_21958.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___170_21958.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21953 wl
                 | (FStar_Syntax_Syntax.Comp uu____21965,
                    FStar_Syntax_Syntax.Comp uu____21966) ->
                     let uu____21967 =
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
                               FStar_TypeChecker_Common.SUB)) in
                     if uu____21967
                     then
                       let uu____21968 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____21968 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21974 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21984 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____21985 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____21984, uu____21985)) in
                          match uu____21974 with
                          | (c1_comp1, c2_comp1) ->
                              solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____21992 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____21992
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21994 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____21994 with
                            | FStar_Pervasives_Native.None ->
                                let uu____21997 =
                                  let uu____21998 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name in
                                  let uu____21999 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____21998 uu____21999 in
                                giveup env uu____21997 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g ->
    let uu____22004 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____22042 ->
              match uu____22042 with
              | (uu____22055, uu____22056, u, uu____22058, uu____22059,
                 uu____22060) -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____22004 (FStar_String.concat ", ")
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,
    (FStar_Syntax_Syntax.universe, FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2 Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs ->
    let vars =
      let uu____22091 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____22091 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____22109 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____22137 ->
                match uu____22137 with
                | (u1, u2) ->
                    let uu____22144 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____22145 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____22144 uu____22145)) in
      FStar_All.pipe_right uu____22109 (FStar_String.concat ", ") in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
let (guard_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun env ->
    fun g ->
      match ((g.FStar_TypeChecker_Env.guard_f),
              (g.FStar_TypeChecker_Env.deferred),
              (g.FStar_TypeChecker_Env.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial, [], (uu____22162, [])) -> "{}"
      | uu____22187 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____22204 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____22204
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____22207 =
              FStar_List.map
                (fun uu____22217 ->
                   match uu____22217 with
                   | (uu____22222, x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____22207 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____22227 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____22227 imps
let new_t_problem :
  'Auu____22235 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____22235 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term, 'Auu____22235)
                  FStar_TypeChecker_Common.problem
  =
  fun env ->
    fun lhs ->
      fun rel ->
        fun rhs ->
          fun elt ->
            fun loc ->
              let reason =
                let uu____22269 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____22269
                then
                  let uu____22270 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____22271 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____22270
                    (rel_to_string rel) uu____22271
                else "TOP" in
              let p = new_problem env lhs rel rhs elt loc reason in p
let (new_t_prob :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.term ->
          (FStar_TypeChecker_Common.prob, FStar_Syntax_Syntax.bv)
            FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun t1 ->
      fun rel ->
        fun t2 ->
          let x =
            let uu____22295 =
              let uu____22298 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_91 -> FStar_Pervasives_Native.Some _0_91) uu____22298 in
            FStar_Syntax_Syntax.new_bv uu____22295 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____22307 =
              let uu____22310 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_92 -> FStar_Pervasives_Native.Some _0_92) uu____22310 in
            let uu____22313 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____22307 uu____22313 in
          ((FStar_TypeChecker_Common.TProb p), x)
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob, Prims.string)
         FStar_Pervasives_Native.tuple2 ->
         FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)
        -> FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)
  =
  fun env ->
    fun probs ->
      fun err ->
        let probs1 =
          let uu____22343 = FStar_Options.eager_inference () in
          if uu____22343
          then
            let uu___171_22344 = probs in
            {
              attempting = (uu___171_22344.attempting);
              wl_deferred = (uu___171_22344.wl_deferred);
              ctr = (uu___171_22344.ctr);
              defer_ok = false;
              smt_ok = (uu___171_22344.smt_ok);
              tcenv = (uu___171_22344.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d, s) ->
            ((let uu____22355 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____22355
              then
                let uu____22356 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____22356
              else ());
             (let result = err (d, s) in
              FStar_Syntax_Unionfind.rollback tx; result))
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env ->
    fun g ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____22370 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____22370
            then
              let uu____22371 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____22371
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f in
            (let uu____22375 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____22375
             then
               let uu____22376 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____22376
             else ());
            (let f2 =
               let uu____22379 =
                 let uu____22380 = FStar_Syntax_Util.unmeta f1 in
                 uu____22380.FStar_Syntax_Syntax.n in
               match uu____22379 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____22384 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___172_22385 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___172_22385.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___172_22385.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___172_22385.FStar_TypeChecker_Env.implicits)
             })))
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun prob ->
      fun dopt ->
        match dopt with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some d ->
            let uu____22404 =
              let uu____22405 =
                let uu____22406 =
                  let uu____22407 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____22407
                    (fun _0_93 -> FStar_TypeChecker_Common.NonTrivial _0_93) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____22406;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____22405 in
            FStar_All.pipe_left
              (fun _0_94 -> FStar_Pervasives_Native.Some _0_94) uu____22404
let with_guard_no_simp :
  'Auu____22434 .
    'Auu____22434 ->
      FStar_TypeChecker_Common.prob ->
        FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env ->
    fun prob ->
      fun dopt ->
        match dopt with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some d ->
            let uu____22454 =
              let uu____22455 =
                let uu____22456 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____22456
                  (fun _0_95 -> FStar_TypeChecker_Common.NonTrivial _0_95) in
              {
                FStar_TypeChecker_Env.guard_f = uu____22455;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____22454
let (try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun smt_ok ->
    fun env ->
      fun t1 ->
        fun t2 ->
          (let uu____22494 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____22494
           then
             let uu____22495 = FStar_Syntax_Print.term_to_string t1 in
             let uu____22496 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____22495
               uu____22496
           else ());
          (let prob =
             let uu____22499 =
               let uu____22504 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____22504 in
             FStar_All.pipe_left
               (fun _0_96 -> FStar_TypeChecker_Common.TProb _0_96)
               uu____22499 in
           let g =
             let uu____22512 =
               let uu____22515 = singleton' env prob smt_ok in
               solve_and_commit env uu____22515
                 (fun uu____22517 -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____22512 in
           g)
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____22535 = try_teq true env t1 t2 in
        match uu____22535 with
        | FStar_Pervasives_Native.None ->
            ((let uu____22539 = FStar_TypeChecker_Env.get_range env in
              let uu____22540 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1 in
              FStar_Errors.log_issue uu____22539 uu____22540);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____22547 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____22547
              then
                let uu____22548 = FStar_Syntax_Print.term_to_string t1 in
                let uu____22549 = FStar_Syntax_Print.term_to_string t2 in
                let uu____22550 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____22548
                  uu____22549 uu____22550
              else ());
             g)
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.unit)
  =
  fun env ->
    fun e ->
      fun t1 ->
        fun t2 ->
          let uu____22564 = FStar_TypeChecker_Env.get_range env in
          let uu____22565 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.log_issue uu____22564 uu____22565
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun c1 ->
      fun c2 ->
        (let uu____22582 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____22582
         then
           let uu____22583 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____22584 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____22583
             uu____22584
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____22589 =
             let uu____22594 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____22594 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_97 -> FStar_TypeChecker_Common.CProb _0_97) uu____22589 in
         let uu____22599 =
           let uu____22602 = singleton env prob in
           solve_and_commit env uu____22602
             (fun uu____22604 -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____22599)
let (solve_universe_inequalities' :
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list,
        (FStar_Syntax_Syntax.universe, FStar_Syntax_Syntax.universe)
          FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.unit)
  =
  fun tx ->
    fun env ->
      fun uu____22633 ->
        match uu____22633 with
        | (variables, ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22672 =
                 let uu____22677 =
                   let uu____22678 = FStar_Syntax_Print.univ_to_string u1 in
                   let uu____22679 = FStar_Syntax_Print.univ_to_string u2 in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____22678 uu____22679 in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____22677) in
               let uu____22680 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____22672 uu____22680) in
            let equiv1 v1 v' =
              let uu____22688 =
                let uu____22693 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____22694 = FStar_Syntax_Subst.compress_univ v' in
                (uu____22693, uu____22694) in
              match uu____22688 with
              | (FStar_Syntax_Syntax.U_unif v0, FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22713 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1 ->
                      let uu____22743 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____22743 with
                      | FStar_Syntax_Syntax.U_unif uu____22750 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22779 ->
                                    match uu____22779 with
                                    | (u, v') ->
                                        let uu____22788 = equiv1 v1 v' in
                                        if uu____22788
                                        then
                                          let uu____22791 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____22791 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____22807 -> [])) in
            let uu____22812 =
              let wl =
                let uu___173_22816 = empty_worklist env in
                {
                  attempting = (uu___173_22816.attempting);
                  wl_deferred = (uu___173_22816.wl_deferred);
                  ctr = (uu___173_22816.ctr);
                  defer_ok = false;
                  smt_ok = (uu___173_22816.smt_ok);
                  tcenv = (uu___173_22816.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22834 ->
                      match uu____22834 with
                      | (lb, v1) ->
                          let uu____22841 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1 in
                          (match uu____22841 with
                           | USolved wl1 -> ()
                           | uu____22843 -> fail1 lb v1))) in
            let rec check_ineq uu____22851 =
              match uu____22851 with
              | (u, v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero, uu____22860) -> true
                   | (FStar_Syntax_Syntax.U_succ u0,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name u0,
                      FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif u0,
                      FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name uu____22883,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif uu____22885,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us, uu____22896) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2 -> check_ineq (u2, v2)))
                   | (uu____22903, FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some (fun v3 -> check_ineq (u1, v3)))
                   | uu____22911 -> false) in
            let uu____22916 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22931 ->
                      match uu____22931 with
                      | (u, v1) ->
                          let uu____22938 = check_ineq (u, v1) in
                          if uu____22938
                          then true
                          else
                            ((let uu____22941 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____22941
                              then
                                let uu____22942 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____22943 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____22942
                                  uu____22943
                              else ());
                             false))) in
            if uu____22916
            then ()
            else
              ((let uu____22947 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____22947
                then
                  ((let uu____22949 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22949);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22959 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22959))
                else ());
               (let uu____22969 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22969))
let (solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list,
      (FStar_Syntax_Syntax.universe, FStar_Syntax_Syntax.universe)
        FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.unit)
  =
  fun env ->
    fun ineqs ->
      let tx = FStar_Syntax_Unionfind.new_transaction () in
      solve_universe_inequalities' tx env ineqs;
      FStar_Syntax_Unionfind.commit tx
let rec (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env ->
    fun g ->
      let fail1 uu____23017 =
        match uu____23017 with
        | (d, s) ->
            let msg = explain env d s in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
              (p_loc d) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____23031 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____23031
       then
         let uu____23032 = wl_to_string wl in
         let uu____23033 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____23032 uu____23033
       else ());
      (let g1 =
         let uu____23048 = solve_and_commit env wl fail1 in
         match uu____23048 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___174_23061 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___174_23061.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___174_23061.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___174_23061.FStar_TypeChecker_Env.implicits)
             }
         | uu____23066 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___175_23070 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___175_23070.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___175_23070.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___175_23070.FStar_TypeChecker_Env.implicits)
        }))
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun env ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____23120 = FStar_ST.op_Bang last_proof_ns in
    match uu____23120 with
    | FStar_Pervasives_Native.None ->
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
  fun use_env_range_msg ->
    fun env ->
      fun g ->
        fun use_smt ->
          let debug1 =
            ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel"))
               ||
               (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "SMTQuery")))
              ||
              (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Tac")) in
          let g1 = solve_deferred_constraints env g in
          let ret_g =
            let uu___176_23241 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___176_23241.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___176_23241.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___176_23241.FStar_TypeChecker_Env.implicits)
            } in
          let uu____23242 =
            let uu____23243 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____23243 in
          if uu____23242
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____23251 = FStar_TypeChecker_Env.get_range env in
                     let uu____23252 =
                       let uu____23253 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____23253 in
                     FStar_Errors.diag uu____23251 uu____23252)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   if debug1
                   then
                     (let uu____23257 = FStar_TypeChecker_Env.get_range env in
                      let uu____23258 =
                        let uu____23259 =
                          FStar_Syntax_Print.term_to_string vc1 in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____23259 in
                      FStar_Errors.diag uu____23257 uu____23258)
                   else ();
                   (let uu____23262 = FStar_TypeChecker_Env.get_range env in
                    def_check_closed_in_env uu____23262 "discharge_guard'"
                      env vc1);
                   (let uu____23263 = check_trivial vc1 in
                    match uu____23263 with
                    | FStar_TypeChecker_Common.Trivial ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____23270 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____23271 =
                                let uu____23272 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____23272 in
                              FStar_Errors.diag uu____23270 uu____23271)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____23277 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____23278 =
                                let uu____23279 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____23279 in
                              FStar_Errors.diag uu____23277 uu____23278)
                           else ();
                           (let vcs =
                              let uu____23290 = FStar_Options.use_tactics () in
                              if uu____23290
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____23309 ->
                                     (let uu____23311 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics" in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____23311);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____23313 =
                                   let uu____23320 = FStar_Options.peek () in
                                   (env, vc2, uu____23320) in
                                 [uu____23313]) in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____23354 ->
                                    match uu____23354 with
                                    | (env1, goal, opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal in
                                        let uu____23365 = check_trivial goal1 in
                                        (match uu____23365 with
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
                                                (let uu____23373 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____23374 =
                                                   let uu____23375 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   let uu____23376 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1 in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____23375 uu____23376 in
                                                 FStar_Errors.diag
                                                   uu____23373 uu____23374)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____23379 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____23380 =
                                                   let uu____23381 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____23381 in
                                                 FStar_Errors.diag
                                                   uu____23379 uu____23380)
                                              else ();
                                              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                use_env_range_msg env1 goal2;
                                              FStar_Options.pop ())))));
                           FStar_Pervasives_Native.Some ret_g)))))
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env ->
    fun g ->
      let uu____23391 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____23391 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None ->
          let uu____23397 = FStar_TypeChecker_Env.get_range env in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____23397
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env ->
    fun g ->
      let uu____23404 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____23404 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let (resolve_implicits' :
  Prims.bool ->
    Prims.bool ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun must_total ->
    fun forcelax ->
      fun g ->
        let unresolved u =
          let uu____23423 = FStar_Syntax_Unionfind.find u in
          match uu____23423 with
          | FStar_Pervasives_Native.None -> true
          | uu____23426 -> false in
        let rec until_fixpoint acc implicits =
          let uu____23444 = acc in
          match uu____23444 with
          | (out, changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____23530 = hd1 in
                   (match uu____23530 with
                    | (uu____23543, env, u, tm, k, r) ->
                        let uu____23549 = unresolved u in
                        if uu____23549
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env tm in
                           let env1 =
                             if forcelax
                             then
                               let uu___177_23579 = env in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___177_23579.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___177_23579.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___177_23579.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___177_23579.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___177_23579.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___177_23579.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___177_23579.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___177_23579.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___177_23579.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___177_23579.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___177_23579.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___177_23579.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___177_23579.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___177_23579.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___177_23579.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___177_23579.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___177_23579.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___177_23579.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___177_23579.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___177_23579.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___177_23579.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___177_23579.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___177_23579.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___177_23579.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___177_23579.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___177_23579.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___177_23579.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___177_23579.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___177_23579.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___177_23579.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___177_23579.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___177_23579.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___177_23579.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___177_23579.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___177_23579.FStar_TypeChecker_Env.dep_graph)
                               }
                             else env in
                           (let uu____23582 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck") in
                            if uu____23582
                            then
                              let uu____23583 =
                                FStar_Syntax_Print.uvar_to_string u in
                              let uu____23584 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____23585 =
                                FStar_Syntax_Print.term_to_string k in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____23583 uu____23584 uu____23585
                            else ());
                           (let g1 =
                              try
                                env1.FStar_TypeChecker_Env.check_type_of
                                  must_total env1 tm1 k
                              with
                              | e ->
                                  ((let uu____23596 =
                                      let uu____23605 =
                                        let uu____23612 =
                                          let uu____23613 =
                                            FStar_Syntax_Print.uvar_to_string
                                              u in
                                          let uu____23614 =
                                            FStar_TypeChecker_Normalize.term_to_string
                                              env1 tm1 in
                                          FStar_Util.format2
                                            "Failed while checking implicit %s set to %s"
                                            uu____23613 uu____23614 in
                                        (FStar_Errors.Error_BadImplicit,
                                          uu____23612, r) in
                                      [uu____23605] in
                                    FStar_Errors.add_errors uu____23596);
                                   FStar_Exn.raise e) in
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___180_23628 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___180_23628.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___180_23628.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___180_23628.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____23631 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____23637 ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____23631 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
        let uu___181_23665 = g in
        let uu____23666 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___181_23665.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___181_23665.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___181_23665.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____23666
        }
let (resolve_implicits :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t) =
  fun g -> resolve_implicits' true false g
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t) =
  fun g -> resolve_implicits' false true g
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit) =
  fun env ->
    fun g ->
      let g1 =
        let uu____23720 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____23720 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23733 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____23733
      | (reason, uu____23735, uu____23736, e, t, r)::uu____23740 ->
          let uu____23767 =
            let uu____23772 =
              let uu____23773 = FStar_Syntax_Print.term_to_string t in
              let uu____23774 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format2
                "Failed to resolve implicit argument of type '%s' introduced in %s"
                uu____23773 uu____23774 in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23772) in
          FStar_Errors.raise_error uu____23767 r
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1 ->
    fun u2 ->
      let uu___182_23781 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___182_23781.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___182_23781.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___182_23781.FStar_TypeChecker_Env.implicits)
      }
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env ->
    fun g ->
      let uu____23804 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____23804 with
      | FStar_Pervasives_Native.Some uu____23809 -> true
      | FStar_Pervasives_Native.None -> false
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____23819 = try_teq false env t1 t2 in
        match uu____23819 with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some g -> discharge_guard_nosmt env g
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv, FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu____23839 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____23839
         then
           let uu____23840 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____23841 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23840
             uu____23841
         else ());
        (let uu____23843 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
         match uu____23843 with
         | (prob, x) ->
             let g =
               let uu____23859 =
                 let uu____23862 = singleton' env prob true in
                 solve_and_commit env uu____23862
                   (fun uu____23864 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____23859 in
             ((let uu____23874 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g) in
               if uu____23874
               then
                 let uu____23875 =
                   FStar_TypeChecker_Normalize.term_to_string env t1 in
                 let uu____23876 =
                   FStar_TypeChecker_Normalize.term_to_string env t2 in
                 let uu____23877 =
                   let uu____23878 = FStar_Util.must g in
                   guard_to_string env uu____23878 in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23875 uu____23876 uu____23877
               else ());
              (match g with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   FStar_Pervasives_Native.Some (x, g1))))
let (get_subtyping_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____23906 = check_subtyping env t1 t2 in
        match uu____23906 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____23925 =
              let uu____23926 = FStar_Syntax_Syntax.mk_binder x in
              abstract_guard uu____23926 g in
            FStar_Pervasives_Native.Some uu____23925
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____23938 = check_subtyping env t1 t2 in
        match uu____23938 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____23957 =
              let uu____23958 =
                let uu____23959 = FStar_Syntax_Syntax.mk_binder x in
                [uu____23959] in
              close_guard env uu____23958 g in
            FStar_Pervasives_Native.Some uu____23957
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu____23970 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____23970
         then
           let uu____23971 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____23972 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23971
             uu____23972
         else ());
        (let uu____23974 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
         match uu____23974 with
         | (prob, x) ->
             let g =
               let uu____23984 =
                 let uu____23987 = singleton' env prob false in
                 solve_and_commit env uu____23987
                   (fun uu____23989 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____23984 in
             (match g with
              | FStar_Pervasives_Native.None -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____24000 =
                      let uu____24001 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____24001] in
                    close_guard env uu____24000 g1 in
                  discharge_guard_nosmt env g2))