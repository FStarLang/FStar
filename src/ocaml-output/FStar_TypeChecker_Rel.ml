open Prims
let guard_of_guard_formula:
  FStar_TypeChecker_Common.guard_formula -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    {
      FStar_TypeChecker_Env.guard_f = g;
      FStar_TypeChecker_Env.deferred = [];
      FStar_TypeChecker_Env.univ_ineqs = ([], []);
      FStar_TypeChecker_Env.implicits = []
    }
let guard_form:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Common.guard_formula =
  fun g  -> g.FStar_TypeChecker_Env.guard_f
let is_trivial: FStar_TypeChecker_Env.guard_t -> Prims.bool =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Env.deferred = [];
        FStar_TypeChecker_Env.univ_ineqs = uu____33;
        FStar_TypeChecker_Env.implicits = uu____34;_} -> true
    | uu____61 -> false
let trivial_guard: FStar_TypeChecker_Env.guard_t =
  {
    FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial;
    FStar_TypeChecker_Env.deferred = [];
    FStar_TypeChecker_Env.univ_ineqs = ([], []);
    FStar_TypeChecker_Env.implicits = []
  }
let abstract_guard:
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun x  ->
    fun g  ->
      match g with
      | FStar_Pervasives_Native.None  -> g
      | FStar_Pervasives_Native.Some
          {
            FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
            FStar_TypeChecker_Env.deferred = uu____98;
            FStar_TypeChecker_Env.univ_ineqs = uu____99;
            FStar_TypeChecker_Env.implicits = uu____100;_}
          -> g
      | FStar_Pervasives_Native.Some g1 ->
          let f =
            match g1.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.NonTrivial f -> f
            | uu____126 -> failwith "impossible" in
          let uu____127 =
            let uu___135_128 = g1 in
            let uu____129 =
              let uu____130 =
                let uu____131 =
                  let uu____132 = FStar_Syntax_Syntax.mk_binder x in
                  [uu____132] in
                FStar_Syntax_Util.abs uu____131 f
                  (FStar_Pervasives_Native.Some
                     (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0)) in
              FStar_All.pipe_left
                (fun _0_39  -> FStar_TypeChecker_Common.NonTrivial _0_39)
                uu____130 in
            {
              FStar_TypeChecker_Env.guard_f = uu____129;
              FStar_TypeChecker_Env.deferred =
                (uu___135_128.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___135_128.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___135_128.FStar_TypeChecker_Env.implicits)
            } in
          FStar_Pervasives_Native.Some uu____127
let apply_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___136_142 = g in
          let uu____143 =
            let uu____144 =
              let uu____145 =
                let uu____148 =
                  let uu____149 =
                    let uu____164 =
                      let uu____167 = FStar_Syntax_Syntax.as_arg e in
                      [uu____167] in
                    (f, uu____164) in
                  FStar_Syntax_Syntax.Tm_app uu____149 in
                FStar_Syntax_Syntax.mk uu____148 in
              uu____145 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun _0_40  -> FStar_TypeChecker_Common.NonTrivial _0_40)
              uu____144 in
          {
            FStar_TypeChecker_Env.guard_f = uu____143;
            FStar_TypeChecker_Env.deferred =
              (uu___136_142.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___136_142.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___136_142.FStar_TypeChecker_Env.implicits)
          }
let map_guard:
  FStar_TypeChecker_Env.guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___137_187 = g in
          let uu____188 =
            let uu____189 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____189 in
          {
            FStar_TypeChecker_Env.guard_f = uu____188;
            FStar_TypeChecker_Env.deferred =
              (uu___137_187.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___137_187.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___137_187.FStar_TypeChecker_Env.implicits)
          }
let trivial: FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____194 -> failwith "impossible"
let conj_guard_f:
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) -> g
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let uu____207 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____207
let check_trivial:
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula =
  fun t  ->
    let uu____212 =
      let uu____213 = FStar_Syntax_Util.unmeta t in
      uu____213.FStar_Syntax_Syntax.n in
    match uu____212 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____217 -> FStar_TypeChecker_Common.NonTrivial t
let imp_guard_f:
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) ->
          FStar_TypeChecker_Common.Trivial
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2 in check_trivial imp
let binop_guard:
  (FStar_TypeChecker_Common.guard_formula ->
     FStar_TypeChecker_Common.guard_formula ->
       FStar_TypeChecker_Common.guard_formula)
    ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun f  ->
    fun g1  ->
      fun g2  ->
        let uu____253 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
        {
          FStar_TypeChecker_Env.guard_f = uu____253;
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
let conj_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  = fun g1  -> fun g2  -> binop_guard conj_guard_f g1 g2
let imp_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  = fun g1  -> fun g2  -> binop_guard imp_guard_f g1 g2
let close_guard_univs:
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
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
                       let uu____327 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____327
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___138_329 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___138_329.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___138_329.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___138_329.FStar_TypeChecker_Env.implicits)
            }
let close_forall:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binder Prims.list ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun bs  ->
      fun f  ->
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               let uu____351 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____351
               then f1
               else
                 (let u =
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
let close_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun binders  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___139_367 = g in
            let uu____368 =
              let uu____369 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____369 in
            {
              FStar_TypeChecker_Env.guard_f = uu____368;
              FStar_TypeChecker_Env.deferred =
                (uu___139_367.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___139_367.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___139_367.FStar_TypeChecker_Env.implicits)
            }
let new_uvar:
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun binders  ->
      fun k  ->
        let uv = FStar_Syntax_Unionfind.fresh () in
        match binders with
        | [] ->
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k))
                FStar_Pervasives_Native.None r in
            (uv1, uv1)
        | uu____402 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____427 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____427 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r in
            let uu____435 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                FStar_Pervasives_Native.None r in
            (uu____435, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____466 = FStar_Syntax_Util.type_u () in
        match uu____466 with
        | (t_type,u) ->
            let uu____473 =
              let uu____478 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____478 t_type in
            (match uu____473 with
             | (tt,uu____480) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____514 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____556 -> false
let __proj__UNIV__item___0:
  uvi ->
    (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UNIV _0 -> _0
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs;
  wl_deferred:
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list;
  ctr: Prims.int;
  defer_ok: Prims.bool;
  smt_ok: Prims.bool;
  tcenv: FStar_TypeChecker_Env.env;}
let __proj__Mkworklist__item__attempting:
  worklist -> FStar_TypeChecker_Common.probs =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__attempting
let __proj__Mkworklist__item__wl_deferred:
  worklist ->
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__wl_deferred
let __proj__Mkworklist__item__ctr: worklist -> Prims.int =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} -> __fname__ctr
let __proj__Mkworklist__item__defer_ok: worklist -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__defer_ok
let __proj__Mkworklist__item__smt_ok: worklist -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__smt_ok
let __proj__Mkworklist__item__tcenv: worklist -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} -> __fname__tcenv
type solution =
  | Success of FStar_TypeChecker_Common.deferred
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2
let uu___is_Success: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____750 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____768 -> false
let __proj__Failed__item___0:
  solution ->
    (FStar_TypeChecker_Common.prob,Prims.string)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Failed _0 -> _0
type variance =
  | COVARIANT
  | CONTRAVARIANT
  | INVARIANT
let uu___is_COVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____793 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____798 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____803 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___107_827  ->
    match uu___107_827 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string:
  'Auu____834 . 'Auu____834 -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let uu____843 =
        let uu____844 = FStar_Syntax_Subst.compress t in
        uu____844.FStar_Syntax_Syntax.n in
      match uu____843 with
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let uu____873 = FStar_Syntax_Print.uvar_to_string u in
          let uu____874 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.format2 "(%s:%s)" uu____873 uu____874
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
             FStar_Syntax_Syntax.pos = uu____877;
             FStar_Syntax_Syntax.vars = uu____878;_},args)
          ->
          let uu____924 = FStar_Syntax_Print.uvar_to_string u in
          let uu____925 = FStar_Syntax_Print.term_to_string ty in
          let uu____926 = FStar_Syntax_Print.args_to_string args in
          FStar_Util.format3 "(%s:%s) %s" uu____924 uu____925 uu____926
      | uu____927 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___108_935  ->
      match uu___108_935 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____941 =
            let uu____944 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____945 =
              let uu____948 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____949 =
                let uu____952 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____953 =
                  let uu____956 =
                    let uu____959 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____960 =
                      let uu____963 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____964 =
                        let uu____967 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (FStar_Pervasives_Native.fst
                               p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____968 =
                          let uu____971 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____971] in
                        uu____967 :: uu____968 in
                      uu____963 :: uu____964 in
                    uu____959 :: uu____960 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____956 in
                uu____952 :: uu____953 in
              uu____948 :: uu____949 in
            uu____944 :: uu____945 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____941
      | FStar_TypeChecker_Common.CProb p ->
          let uu____979 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____980 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____979
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____980
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___109_988  ->
      match uu___109_988 with
      | UNIV (u,t) ->
          let x =
            let uu____992 = FStar_Options.hide_uvar_nums () in
            if uu____992
            then "?"
            else
              (let uu____994 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____994 FStar_Util.string_of_int) in
          let uu____995 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____995
      | TERM ((u,uu____997),t) ->
          let x =
            let uu____1004 = FStar_Options.hide_uvar_nums () in
            if uu____1004
            then "?"
            else
              (let uu____1006 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____1006 FStar_Util.string_of_int) in
          let uu____1007 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____1007
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____1020 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____1020 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____1033 =
      let uu____1036 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____1036
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____1033 (FStar_String.concat ", ")
let args_to_string:
  'Auu____1049 .
    (FStar_Syntax_Syntax.term,'Auu____1049) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1066 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1084  ->
              match uu____1084 with
              | (x,uu____1090) -> FStar_Syntax_Print.term_to_string x)) in
    FStar_All.pipe_right uu____1066 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____1097 =
      let uu____1098 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____1098 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1097;
      smt_ok = true;
      tcenv = env
    }
let singleton':
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.bool -> worklist
  =
  fun env  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___140_1117 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___140_1117.wl_deferred);
          ctr = (uu___140_1117.ctr);
          defer_ok = (uu___140_1117.defer_ok);
          smt_ok;
          tcenv = (uu___140_1117.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard:
  'Auu____1132 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1132,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___141_1153 = empty_worklist env in
      let uu____1154 = FStar_List.map FStar_Pervasives_Native.snd g in
      {
        attempting = uu____1154;
        wl_deferred = (uu___141_1153.wl_deferred);
        ctr = (uu___141_1153.ctr);
        defer_ok = false;
        smt_ok = (uu___141_1153.smt_ok);
        tcenv = (uu___141_1153.tcenv)
      }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___142_1171 = wl in
        {
          attempting = (uu___142_1171.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___142_1171.ctr);
          defer_ok = (uu___142_1171.defer_ok);
          smt_ok = (uu___142_1171.smt_ok);
          tcenv = (uu___142_1171.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___143_1190 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___143_1190.wl_deferred);
        ctr = (uu___143_1190.ctr);
        defer_ok = (uu___143_1190.defer_ok);
        smt_ok = (uu___143_1190.smt_ok);
        tcenv = (uu___143_1190.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1204 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____1204
         then
           let uu____1205 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1205
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___110_1210  ->
    match uu___110_1210 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert:
  'Auu____1217 'Auu____1218 .
    ('Auu____1218,'Auu____1217) FStar_TypeChecker_Common.problem ->
      ('Auu____1218,'Auu____1217) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___144_1235 = p in
    {
      FStar_TypeChecker_Common.pid =
        (uu___144_1235.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___144_1235.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___144_1235.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___144_1235.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___144_1235.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___144_1235.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___144_1235.FStar_TypeChecker_Common.rank)
    }
let maybe_invert:
  'Auu____1246 'Auu____1247 .
    ('Auu____1247,'Auu____1246) FStar_TypeChecker_Common.problem ->
      ('Auu____1247,'Auu____1246) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___111_1268  ->
    match uu___111_1268 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___112_1294  ->
      match uu___112_1294 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___113_1298  ->
    match uu___113_1298 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___114_1312  ->
    match uu___114_1312 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___115_1328  ->
    match uu___115_1328 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___116_1344  ->
    match uu___116_1344 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___117_1362  ->
    match uu___117_1362 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___118_1380  ->
    match uu___118_1380 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___119_1394  ->
    match uu___119_1394 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____1417 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1417 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1430  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr
let mk_problem:
  'Auu____1495 'Auu____1496 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1496 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1496 ->
              'Auu____1495 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1496,'Auu____1495)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1533 = next_pid () in
                let uu____1534 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1533;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1534;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let new_problem:
  'Auu____1557 'Auu____1558 .
    FStar_TypeChecker_Env.env ->
      'Auu____1558 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1558 ->
            'Auu____1557 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1558,'Auu____1557)
                    FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              fun reason  ->
                let scope = FStar_TypeChecker_Env.all_binders env in
                let uu____1596 = next_pid () in
                let uu____1597 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1596;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1597;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let problem_using_guard:
  'Auu____1618 'Auu____1619 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1619 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1619 ->
            'Auu____1618 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1619,'Auu____1618) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____1652 = next_pid () in
              {
                FStar_TypeChecker_Common.pid = uu____1652;
                FStar_TypeChecker_Common.lhs = lhs;
                FStar_TypeChecker_Common.relation = rel;
                FStar_TypeChecker_Common.rhs = rhs;
                FStar_TypeChecker_Common.element = elt;
                FStar_TypeChecker_Common.logical_guard = (p_guard orig);
                FStar_TypeChecker_Common.scope = (p_scope orig);
                FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
                FStar_TypeChecker_Common.loc = (p_loc orig);
                FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
              }
let guard_on_element:
  'Auu____1663 .
    worklist ->
      ('Auu____1663,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
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
                  x.FStar_Syntax_Syntax.sort in
              FStar_Syntax_Util.mk_forall u x phi
          | FStar_Pervasives_Native.Some e ->
              FStar_Syntax_Subst.subst [FStar_Syntax_Syntax.NT (x, e)] phi
let explain:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____1716 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1716
        then
          let uu____1717 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1718 = prob_to_string env d in
          let uu____1719 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1717 uu____1718 uu____1719 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1725 -> failwith "impossible" in
           let uu____1726 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1740 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1741 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1740, uu____1741)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1747 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1748 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1747, uu____1748) in
           match uu____1726 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___120_1765  ->
            match uu___120_1765 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1777 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1779),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___121_1801  ->
           match uu___121_1801 with
           | UNIV uu____1804 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1810),t) ->
               let uu____1816 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1816
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___122_1838  ->
           match uu___122_1838 with
           | UNIV (u',t) ->
               let uu____1843 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1843
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1847 -> FStar_Pervasives_Native.None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1856 =
        let uu____1857 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1857 in
      FStar_Syntax_Subst.compress uu____1856
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1866 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1866
let norm_arg:
  'Auu____1873 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____1873) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1873)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____1894 = sn env (FStar_Pervasives_Native.fst t) in
      (uu____1894, (FStar_Pervasives_Native.snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1927  ->
              match uu____1927 with
              | (x,imp) ->
                  let uu____1938 =
                    let uu___145_1939 = x in
                    let uu____1940 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___145_1939.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___145_1939.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1940
                    } in
                  (uu____1938, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1957 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1957
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1961 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1961
        | uu____1964 -> u2 in
      let uu____1965 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1965
let normalize_refinement:
  'Auu____1976 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____1976 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun steps  ->
    fun env  ->
      fun wl  ->
        fun t0  ->
          FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement:
  'Auu____2001 .
    FStar_TypeChecker_Env.env ->
      'Auu____2001 ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.bv,
                                                                  FStar_Syntax_Syntax.term'
                                                                    FStar_Syntax_Syntax.syntax)
                                                                  FStar_Pervasives_Native.tuple2
                                                                  FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun t1  ->
        let rec aux norm1 t11 =
          match t11.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____2106 =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 match uu____2106 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2123;
                     FStar_Syntax_Syntax.vars = uu____2124;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2150 =
                       let uu____2151 = FStar_Syntax_Print.term_to_string tt in
                       let uu____2152 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2151 uu____2152 in
                     failwith uu____2150)
          | FStar_Syntax_Syntax.Tm_uinst uu____2167 ->
              if norm1
              then (t11, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 let uu____2206 =
                   let uu____2207 = FStar_Syntax_Subst.compress t1' in
                   uu____2207.FStar_Syntax_Syntax.n in
                 match uu____2206 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2224 -> aux true t1'
                 | uu____2231 -> (t11, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2248 ->
              if norm1
              then (t11, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 let uu____2281 =
                   let uu____2282 = FStar_Syntax_Subst.compress t1' in
                   uu____2282.FStar_Syntax_Syntax.n in
                 match uu____2281 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2299 -> aux true t1'
                 | uu____2306 -> (t11, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2323 ->
              if norm1
              then (t11, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 let uu____2370 =
                   let uu____2371 = FStar_Syntax_Subst.compress t1' in
                   uu____2371.FStar_Syntax_Syntax.n in
                 match uu____2370 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2388 -> aux true t1'
                 | uu____2395 -> (t11, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2412 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2429 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2446 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2463 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2480 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2509 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2542 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2575 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2604 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2643 ->
              let uu____2650 =
                let uu____2651 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2652 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2651 uu____2652 in
              failwith uu____2650
          | FStar_Syntax_Syntax.Tm_ascribed uu____2667 ->
              let uu____2694 =
                let uu____2695 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2696 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2695 uu____2696 in
              failwith uu____2694
          | FStar_Syntax_Syntax.Tm_delayed uu____2711 ->
              let uu____2736 =
                let uu____2737 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2738 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2737 uu____2738 in
              failwith uu____2736
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2753 =
                let uu____2754 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2755 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2754 uu____2755 in
              failwith uu____2753 in
        let uu____2770 = whnf env t1 in aux false uu____2770
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun t  ->
      let uu____2781 =
        let uu____2796 = empty_worklist env in
        base_and_refinement env uu____2796 t in
      FStar_All.pipe_right uu____2781 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2831 = FStar_Syntax_Syntax.null_bv t in
    (uu____2831, FStar_Syntax_Util.t_true)
let as_refinement:
  'Auu____2840 .
    FStar_TypeChecker_Env.env ->
      'Auu____2840 ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun t  ->
        let uu____2857 = base_and_refinement env wl t in
        match uu____2857 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
let force_refinement:
  (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                              FStar_Pervasives_Native.tuple2
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun uu____2937  ->
    match uu____2937 with
    | (t_base,refopt) ->
        let uu____2964 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
        (match uu____2964 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___123_2994  ->
      match uu___123_2994 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____3000 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____3001 =
            let uu____3002 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____3002 in
          let uu____3003 =
            let uu____3004 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____3004 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____3000 uu____3001
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____3003
      | FStar_TypeChecker_Common.CProb p ->
          let uu____3010 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____3011 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____3012 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____3010 uu____3011
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____3012
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____3017 =
      let uu____3020 =
        let uu____3023 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3046  ->
                  match uu____3046 with | (uu____3053,uu____3054,x) -> x)) in
        FStar_List.append wl.attempting uu____3023 in
      FStar_List.map (wl_prob_to_string wl) uu____3020 in
    FStar_All.pipe_right uu____3017 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3082 =
          let uu____3101 =
            let uu____3102 = FStar_Syntax_Subst.compress k in
            uu____3102.FStar_Syntax_Syntax.n in
          match uu____3101 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3167 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____3167)
              else
                (let uu____3193 = FStar_Syntax_Util.abs_formals t in
                 match uu____3193 with
                 | (ys',t1,uu____3222) ->
                     let uu____3227 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3227))
          | uu____3268 ->
              let uu____3269 =
                let uu____3280 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3280) in
              ((ys, t), uu____3269) in
        match uu____3082 with
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
                 let uu____3359 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3359 c in
               FStar_Syntax_Util.abs ys1 t1
                 (FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_comp_of_comp c1)))
let solve_prob':
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        uvi Prims.list -> worklist -> worklist
  =
  fun resolve_ok  ->
    fun prob  ->
      fun logical_guard  ->
        fun uvis  ->
          fun wl  ->
            let phi =
              match logical_guard with
              | FStar_Pervasives_Native.None  -> FStar_Syntax_Util.t_true
              | FStar_Pervasives_Native.Some phi -> phi in
            let uu____3392 = p_guard prob in
            match uu____3392 with
            | (uu____3397,uv) ->
                ((let uu____3400 =
                    let uu____3401 = FStar_Syntax_Subst.compress uv in
                    uu____3401.FStar_Syntax_Syntax.n in
                  match uu____3400 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3433 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3433
                        then
                          let uu____3434 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3435 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3436 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3434
                            uu____3435 uu____3436
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3438 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___146_3441 = wl in
                  {
                    attempting = (uu___146_3441.attempting);
                    wl_deferred = (uu___146_3441.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___146_3441.defer_ok);
                    smt_ok = (uu___146_3441.smt_ok);
                    tcenv = (uu___146_3441.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3459 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3459
         then
           let uu____3460 = FStar_Util.string_of_int pid in
           let uu____3461 =
             let uu____3462 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3462 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3460 uu____3461
         else ());
        commit sol;
        (let uu___147_3469 = wl in
         {
           attempting = (uu___147_3469.attempting);
           wl_deferred = (uu___147_3469.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___147_3469.defer_ok);
           smt_ok = (uu___147_3469.smt_ok);
           tcenv = (uu___147_3469.tcenv)
         })
let solve_prob:
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      uvi Prims.list -> worklist -> worklist
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          let conj_guard1 t g =
            match (t, g) with
            | (uu____3511,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3523 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3523 in
          (let uu____3529 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3529
           then
             let uu____3530 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3531 =
               let uu____3532 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3532 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3530 uu____3531
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs:
  'b .
    worklist ->
      (FStar_Syntax_Syntax.uvar,'b) FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun wl  ->
    fun uk  ->
      fun t  ->
        let uu____3567 =
          let uu____3574 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3574 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3567
          (FStar_Util.for_some
             (fun uu____3610  ->
                match uu____3610 with
                | (uv,uu____3616) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check:
  'Auu____3629 'Auu____3630 .
    'Auu____3630 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3629)
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
            let uu____3662 = occurs wl uk t in Prims.op_Negation uu____3662 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3669 =
                 let uu____3670 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3671 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3670 uu____3671 in
               FStar_Pervasives_Native.Some uu____3669) in
          (occurs_ok, msg)
let occurs_and_freevars_check:
  'Auu____3688 'Auu____3689 .
    'Auu____3689 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3688)
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
            let fvs_t = FStar_Syntax_Free.names t in
            let uu____3743 = occurs_check env wl uk t in
            match uu____3743 with
            | (occurs_ok,msg) ->
                let uu____3774 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3774, (msg, fvs, fvs_t))
let intersect_vars:
  'Auu____3801 'Auu____3802 .
    (FStar_Syntax_Syntax.bv,'Auu____3802) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3801) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3801) FStar_Pervasives_Native.tuple2
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
             FStar_Syntax_Syntax.no_names) in
      let v1_set = as_set1 v1 in
      let uu____3886 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3940  ->
                fun uu____3941  ->
                  match (uu____3940, uu____3941) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____4022 =
                        let uu____4023 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____4023 in
                      if uu____4022
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____4048 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____4048
                         then
                           let uu____4061 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____4061)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3886 with | (isect,uu____4102) -> FStar_List.rev isect
let binders_eq:
  'Auu____4131 'Auu____4132 .
    (FStar_Syntax_Syntax.bv,'Auu____4132) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4131) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4187  ->
              fun uu____4188  ->
                match (uu____4187, uu____4188) with
                | ((a,uu____4206),(b,uu____4208)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt:
  'Auu____4227 'Auu____4228 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____4228) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____4227)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____4227)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4279 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4293  ->
                      match uu____4293 with
                      | (b,uu____4299) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____4279
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4315 -> FStar_Pervasives_Native.None
let rec pat_vars:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun args  ->
        match args with
        | [] -> FStar_Pervasives_Native.Some (FStar_List.rev seen)
        | hd1::rest ->
            let uu____4390 = pat_var_opt env seen hd1 in
            (match uu____4390 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4404 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4404
                   then
                     let uu____4405 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4405
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4424 =
      let uu____4425 = FStar_Syntax_Subst.compress t in
      uu____4425.FStar_Syntax_Syntax.n in
    match uu____4424 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4428 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4445;
           FStar_Syntax_Syntax.pos = uu____4446;
           FStar_Syntax_Syntax.vars = uu____4447;_},uu____4448)
        -> true
    | uu____4485 -> false
let destruct_flex_t:
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
      FStar_Pervasives_Native.tuple4
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
           FStar_Syntax_Syntax.pos = uu____4610;
           FStar_Syntax_Syntax.vars = uu____4611;_},args)
        -> (t, uv, k, args)
    | uu____4679 -> failwith "Not a flex-uvar"
let destruct_flex_pattern:
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
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____4758 = destruct_flex_t t in
      match uu____4758 with
      | (t1,uv,k,args) ->
          let uu____4873 = pat_vars env [] args in
          (match uu____4873 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4971 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5053 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5090 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5095 -> false
let head_match: match_result -> match_result =
  fun uu___124_5099  ->
    match uu___124_5099 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5114 -> HeadMatch
let fv_delta_depth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth
  =
  fun env  ->
    fun fv  ->
      match fv.FStar_Syntax_Syntax.fv_delta with
      | FStar_Syntax_Syntax.Delta_abstract d ->
          if
            (env.FStar_TypeChecker_Env.curmodule).FStar_Ident.str =
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
          then d
          else FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5125 ->
          let uu____5126 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____5126 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5137 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____5158 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5167 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5194 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5195 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5196 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5213 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5226 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5250) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5256,uu____5257) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5299) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5320;
             FStar_Syntax_Syntax.index = uu____5321;
             FStar_Syntax_Syntax.sort = t2;_},uu____5323)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5330 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5331 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5332 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5345 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5363 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5363
let rec head_matches:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> match_result
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let t11 = FStar_Syntax_Util.unmeta t1 in
        let t21 = FStar_Syntax_Util.unmeta t2 in
        match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____5387 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5387
            then FullMatch
            else
              (let uu____5389 =
                 let uu____5398 =
                   let uu____5401 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5401 in
                 let uu____5402 =
                   let uu____5405 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5405 in
                 (uu____5398, uu____5402) in
               MisMatch uu____5389)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5411),FStar_Syntax_Syntax.Tm_uinst (g,uu____5413)) ->
            let uu____5422 = head_matches env f g in
            FStar_All.pipe_right uu____5422 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5431),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5433)) ->
            let uu____5482 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5482
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5489),FStar_Syntax_Syntax.Tm_refine (y,uu____5491)) ->
            let uu____5500 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5500 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5502),uu____5503) ->
            let uu____5508 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5508 head_match
        | (uu____5509,FStar_Syntax_Syntax.Tm_refine (x,uu____5511)) ->
            let uu____5516 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5516 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5517,FStar_Syntax_Syntax.Tm_type
           uu____5518) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5519,FStar_Syntax_Syntax.Tm_arrow uu____5520) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5546),FStar_Syntax_Syntax.Tm_app (head',uu____5548))
            ->
            let uu____5589 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5589 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5591),uu____5592) ->
            let uu____5613 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5613 head_match
        | (uu____5614,FStar_Syntax_Syntax.Tm_app (head1,uu____5616)) ->
            let uu____5637 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5637 head_match
        | uu____5638 ->
            let uu____5643 =
              let uu____5652 = delta_depth_of_term env t11 in
              let uu____5655 = delta_depth_of_term env t21 in
              (uu____5652, uu____5655) in
            MisMatch uu____5643
let head_matches_delta:
  'Auu____5672 .
    FStar_TypeChecker_Env.env ->
      'Auu____5672 ->
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
            let uu____5705 = FStar_Syntax_Util.head_and_args t in
            match uu____5705 with
            | (head1,uu____5723) ->
                let uu____5744 =
                  let uu____5745 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5745.FStar_Syntax_Syntax.n in
                (match uu____5744 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5751 =
                       let uu____5752 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5752 FStar_Option.isSome in
                     if uu____5751
                     then
                       let uu____5771 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5771
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____5775 -> FStar_Pervasives_Native.None) in
          let success d r t11 t21 =
            (r,
              (if d > (Prims.parse_int "0")
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None)) in
          let fail r = (r, FStar_Pervasives_Native.None) in
          let rec aux retry n_delta t11 t21 =
            let r = head_matches env t11 t21 in
            match r with
            | MisMatch
                (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5878)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5896 =
                     let uu____5905 = maybe_inline t11 in
                     let uu____5908 = maybe_inline t21 in
                     (uu____5905, uu____5908) in
                   match uu____5896 with
                   | (FStar_Pervasives_Native.None
                      ,FStar_Pervasives_Native.None ) -> fail r
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
                (uu____5945,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5963 =
                     let uu____5972 = maybe_inline t11 in
                     let uu____5975 = maybe_inline t21 in
                     (uu____5972, uu____5975) in
                   match uu____5963 with
                   | (FStar_Pervasives_Native.None
                      ,FStar_Pervasives_Native.None ) -> fail r
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
                let uu____6018 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____6018 with
                 | FStar_Pervasives_Native.None  -> fail r
                 | FStar_Pervasives_Native.Some d ->
                     let t12 =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d;
                         FStar_TypeChecker_Normalize.WHNF] env wl t11 in
                     let t22 =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d;
                         FStar_TypeChecker_Normalize.WHNF] env wl t21 in
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch
                (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                 d2)
                ->
                let d1_greater_than_d2 =
                  FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
                let uu____6041 =
                  if d1_greater_than_d2
                  then
                    let t1' =
                      normalize_refinement
                        [FStar_TypeChecker_Normalize.UnfoldUntil d2;
                        FStar_TypeChecker_Normalize.WHNF] env wl t11 in
                    (t1', t21)
                  else
                    (let t2' =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                         FStar_TypeChecker_Normalize.WHNF] env wl t21 in
                     (t11, t2')) in
                (match uu____6041 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6065 -> fail r
            | uu____6074 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____6108 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____6146 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6165 = FStar_Syntax_Util.type_u () in
      match uu____6165 with
      | (t,uu____6171) ->
          let uu____6172 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____6172
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6185 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____6185 FStar_Pervasives_Native.fst
let rec decompose:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (tc Prims.list -> FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term ->
                                                   Prims.bool,(FStar_Syntax_Syntax.binder
                                                                 FStar_Pervasives_Native.option,
                                                                variance,
                                                                tc)
                                                                FStar_Pervasives_Native.tuple3
                                                                Prims.list)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let matches t' =
        let uu____6251 = head_matches env t1 t' in
        match uu____6251 with
        | MisMatch uu____6252 -> false
        | uu____6261 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6357,imp),T (t2,uu____6360)) -> (t2, imp)
                     | uu____6379 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6446  ->
                    match uu____6446 with
                    | (t2,uu____6460) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6503 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6503 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6578))::tcs2) ->
                       aux
                         (((let uu___148_6613 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_6613.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_6613.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6631 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___125_6684 =
                 match uu___125_6684 with
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
               let uu____6801 = decompose1 [] bs1 in
               (rebuild, matches, uu____6801))
      | uu____6850 ->
          let rebuild uu___126_6856 =
            match uu___126_6856 with
            | [] -> t1
            | uu____6859 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___127_6891  ->
    match uu___127_6891 with
    | T (t,uu____6893) -> t
    | uu____6902 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___128_6906  ->
    match uu___128_6906 with
    | T (t,uu____6908) -> FStar_Syntax_Syntax.as_arg t
    | uu____6917 -> failwith "Impossible"
let imitation_sub_probs:
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.args ->
          (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,
            variance,tc) FStar_Pervasives_Native.tuple3 Prims.list ->
            (FStar_TypeChecker_Common.prob Prims.list,tc Prims.list,FStar_Syntax_Syntax.formula)
              FStar_Pervasives_Native.tuple3
  =
  fun orig  ->
    fun env  ->
      fun scope  ->
        fun ps  ->
          fun qs  ->
            let r = p_loc orig in
            let rel = p_rel orig in
            let sub_prob scope1 args q =
              match q with
              | (uu____7028,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____7053 = new_uvar r scope1 k in
                  (match uu____7053 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7071 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____7088 =
                         let uu____7089 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____7089 in
                       ((T (gi_xs, mk_kind)), uu____7088))
              | (uu____7102,uu____7103,C uu____7104) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7251 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7268;
                         FStar_Syntax_Syntax.vars = uu____7269;_})
                        ->
                        let uu____7292 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7292 with
                         | (T (gi_xs,uu____7316),prob) ->
                             let uu____7326 =
                               let uu____7327 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____7327 in
                             (uu____7326, [prob])
                         | uu____7330 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7345;
                         FStar_Syntax_Syntax.vars = uu____7346;_})
                        ->
                        let uu____7369 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7369 with
                         | (T (gi_xs,uu____7393),prob) ->
                             let uu____7403 =
                               let uu____7404 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7404 in
                             (uu____7403, [prob])
                         | uu____7407 -> failwith "impossible")
                    | (uu____7418,uu____7419,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7421;
                         FStar_Syntax_Syntax.vars = uu____7422;_})
                        ->
                        let components =
                          FStar_All.pipe_right
                            c.FStar_Syntax_Syntax.effect_args
                            (FStar_List.map
                               (fun t  ->
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
                        let uu____7553 =
                          let uu____7562 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7562 FStar_List.unzip in
                        (match uu____7553 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7616 =
                                 let uu____7617 =
                                   let uu____7620 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7620 un_T in
                                 let uu____7621 =
                                   let uu____7630 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7630
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7617;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7621;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7616 in
                             ((C gi_xs), sub_probs))
                    | uu____7639 ->
                        let uu____7652 = sub_prob scope1 args q in
                        (match uu____7652 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____7251 with
                   | (tc,probs) ->
                       let uu____7683 =
                         match q with
                         | (FStar_Pervasives_Native.Some
                            b,uu____7733,uu____7734) ->
                             let uu____7749 =
                               let uu____7756 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____7756 :: args in
                             ((FStar_Pervasives_Native.Some b), (b ::
                               scope1), uu____7749)
                         | uu____7791 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7683 with
                        | (bopt,scope2,args1) ->
                            let uu____7871 = aux scope2 args1 qs2 in
                            (match uu____7871 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7908 =
                                         let uu____7911 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____7911 in
                                       FStar_Syntax_Util.mk_conj_l uu____7908
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____7934 =
                                         let uu____7937 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____7938 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____7937 :: uu____7938 in
                                       FStar_Syntax_Util.mk_conj_l uu____7934 in
                                 ((FStar_List.append probs sub_probs), (tc ::
                                   tcs), f1)))) in
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
let rigid_rigid: Prims.int = Prims.parse_int "0"
let flex_rigid_eq: Prims.int = Prims.parse_int "1"
let flex_refine_inner: Prims.int = Prims.parse_int "2"
let flex_refine: Prims.int = Prims.parse_int "3"
let flex_rigid: Prims.int = Prims.parse_int "4"
let rigid_flex: Prims.int = Prims.parse_int "5"
let refine_flex: Prims.int = Prims.parse_int "6"
let flex_flex: Prims.int = Prims.parse_int "7"
let compress_tprob:
  'Auu____8009 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8009)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8009)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___149_8030 = p in
      let uu____8035 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____8036 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___149_8030.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8035;
        FStar_TypeChecker_Common.relation =
          (uu___149_8030.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8036;
        FStar_TypeChecker_Common.element =
          (uu___149_8030.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___149_8030.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___149_8030.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___149_8030.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___149_8030.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___149_8030.FStar_TypeChecker_Common.rank)
      }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8050 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____8050
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____8059 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8081 = compress_prob wl pr in
        FStar_All.pipe_right uu____8081 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8091 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8091 with
           | (lh,uu____8111) ->
               let uu____8132 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8132 with
                | (rh,uu____8152) ->
                    let uu____8173 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8190,FStar_Syntax_Syntax.Tm_uvar uu____8191)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8228,uu____8229)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8250,FStar_Syntax_Syntax.Tm_uvar uu____8251)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8272,uu____8273)
                          ->
                          let uu____8290 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____8290 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8353 ->
                                    let rank =
                                      let uu____8363 = is_top_level_prob prob in
                                      if uu____8363
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8365 =
                                      let uu___150_8370 = tp in
                                      let uu____8375 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___150_8370.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___150_8370.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___150_8370.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8375;
                                        FStar_TypeChecker_Common.element =
                                          (uu___150_8370.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___150_8370.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___150_8370.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___150_8370.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___150_8370.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___150_8370.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8365)))
                      | (uu____8390,FStar_Syntax_Syntax.Tm_uvar uu____8391)
                          ->
                          let uu____8408 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8408 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8471 ->
                                    let uu____8480 =
                                      let uu___151_8487 = tp in
                                      let uu____8492 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___151_8487.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8492;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___151_8487.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___151_8487.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___151_8487.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___151_8487.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___151_8487.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___151_8487.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___151_8487.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___151_8487.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8480)))
                      | (uu____8513,uu____8514) -> (rigid_rigid, tp) in
                    (match uu____8173 with
                     | (rank,tp1) ->
                         let uu____8533 =
                           FStar_All.pipe_right
                             (let uu___152_8539 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___152_8539.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___152_8539.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___152_8539.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___152_8539.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___152_8539.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___152_8539.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___152_8539.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___152_8539.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___152_8539.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50) in
                         (rank, uu____8533))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8549 =
            FStar_All.pipe_right
              (let uu___153_8555 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___153_8555.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___153_8555.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___153_8555.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___153_8555.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___153_8555.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___153_8555.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___153_8555.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___153_8555.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___153_8555.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51) in
          (rigid_rigid, uu____8549)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____8611 probs =
      match uu____8611 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8664 = rank wl hd1 in
               (match uu____8664 with
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
                      else aux (min_rank, min1, (hd2 :: out)) tl1)) in
    aux
      ((flex_flex + (Prims.parse_int "1")), FStar_Pervasives_Native.None, [])
      wl.attempting
let is_flex_rigid: Prims.int -> Prims.bool =
  fun rank1  -> (flex_refine_inner <= rank1) && (rank1 <= flex_rigid)
let is_rigid_flex: Prims.int -> Prims.bool =
  fun rank1  -> (rigid_flex <= rank1) && (rank1 <= refine_flex)
type univ_eq_sol =
  | UDeferred of worklist
  | USolved of worklist
  | UFailed of Prims.string
let uu___is_UDeferred: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____8774 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8788 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8802 -> false
let __proj__UFailed__item___0: univ_eq_sol -> Prims.string =
  fun projectee  -> match projectee with | UFailed _0 -> _0
let rec really_solve_universe_eq:
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol
  =
  fun pid_orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          let u11 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1 in
          let u21 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2 in
          let rec occurs_univ v1 u =
            match u with
            | FStar_Syntax_Syntax.U_max us ->
                FStar_All.pipe_right us
                  (FStar_Util.for_some
                     (fun u3  ->
                        let uu____8847 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8847 with
                        | (k,uu____8853) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8863 -> false)))
            | uu____8864 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____8915 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____8915 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8918 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____8928 =
                     let uu____8929 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____8930 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8929
                       uu____8930 in
                   UFailed uu____8928)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8950 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8950 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8972 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8972 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____8975 ->
                let uu____8980 =
                  let uu____8981 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____8982 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8981
                    uu____8982 msg in
                UFailed uu____8980 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8983,uu____8984) ->
              let uu____8985 =
                let uu____8986 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8987 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8986 uu____8987 in
              failwith uu____8985
          | (FStar_Syntax_Syntax.U_unknown ,uu____8988) ->
              let uu____8989 =
                let uu____8990 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8991 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8990 uu____8991 in
              failwith uu____8989
          | (uu____8992,FStar_Syntax_Syntax.U_bvar uu____8993) ->
              let uu____8994 =
                let uu____8995 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8996 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8995 uu____8996 in
              failwith uu____8994
          | (uu____8997,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8998 =
                let uu____8999 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9000 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8999 uu____9000 in
              failwith uu____8998
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9024 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____9024
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____9046 = occurs_univ v1 u3 in
              if uu____9046
              then
                let uu____9047 =
                  let uu____9048 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9049 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9048 uu____9049 in
                try_umax_components u11 u21 uu____9047
              else
                (let uu____9051 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9051)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9071 = occurs_univ v1 u3 in
              if uu____9071
              then
                let uu____9072 =
                  let uu____9073 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9074 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9073 uu____9074 in
                try_umax_components u11 u21 uu____9072
              else
                (let uu____9076 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9076)
          | (FStar_Syntax_Syntax.U_max uu____9085,uu____9086) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9092 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9092
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9094,FStar_Syntax_Syntax.U_max uu____9095) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9101 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9101
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9103,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9104,FStar_Syntax_Syntax.U_name
             uu____9105) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9106) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9107) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9108,FStar_Syntax_Syntax.U_succ
             uu____9109) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9110,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
let solve_universe_eq:
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol
  =
  fun orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          if (wl.tcenv).FStar_TypeChecker_Env.lax_universes
          then USolved wl
          else really_solve_universe_eq orig wl u1 u2
let match_num_binders:
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
      let uu____9204 = bc1 in
      match uu____9204 with
      | (bs1,mk_cod1) ->
          let uu____9245 = bc2 in
          (match uu____9245 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____9315 = FStar_Util.first_N n1 bs in
                 match uu____9315 with
                 | (bs3,rest) ->
                     let uu____9340 = mk_cod rest in (bs3, uu____9340) in
               let l1 = FStar_List.length bs1 in
               let l2 = FStar_List.length bs2 in
               if l1 = l2
               then
                 let uu____9369 =
                   let uu____9376 = mk_cod1 [] in (bs1, uu____9376) in
                 let uu____9379 =
                   let uu____9386 = mk_cod2 [] in (bs2, uu____9386) in
                 (uu____9369, uu____9379)
               else
                 if l1 > l2
                 then
                   (let uu____9428 = curry l2 bs1 mk_cod1 in
                    let uu____9441 =
                      let uu____9448 = mk_cod2 [] in (bs2, uu____9448) in
                    (uu____9428, uu____9441))
                 else
                   (let uu____9464 =
                      let uu____9471 = mk_cod1 [] in (bs1, uu____9471) in
                    let uu____9474 = curry l1 bs2 mk_cod2 in
                    (uu____9464, uu____9474)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____9595 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9595
       then
         let uu____9596 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9596
       else ());
      (let uu____9598 = next_prob probs in
       match uu____9598 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___154_9619 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___154_9619.wl_deferred);
               ctr = (uu___154_9619.ctr);
               defer_ok = (uu___154_9619.defer_ok);
               smt_ok = (uu___154_9619.smt_ok);
               tcenv = (uu___154_9619.tcenv)
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
                  let uu____9630 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9630 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9635 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9635 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9640,uu____9641) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9658 ->
                let uu____9667 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9726  ->
                          match uu____9726 with
                          | (c,uu____9734,uu____9735) -> c < probs.ctr)) in
                (match uu____9667 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9776 =
                            FStar_List.map
                              (fun uu____9791  ->
                                 match uu____9791 with
                                 | (uu____9802,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____9776
                      | uu____9805 ->
                          let uu____9814 =
                            let uu___155_9815 = probs in
                            let uu____9816 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9837  ->
                                      match uu____9837 with
                                      | (uu____9844,uu____9845,y) -> y)) in
                            {
                              attempting = uu____9816;
                              wl_deferred = rest;
                              ctr = (uu___155_9815.ctr);
                              defer_ok = (uu___155_9815.defer_ok);
                              smt_ok = (uu___155_9815.smt_ok);
                              tcenv = (uu___155_9815.tcenv)
                            } in
                          solve env uu____9814))))
and solve_one_universe_eq:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> worklist -> solution
  =
  fun env  ->
    fun orig  ->
      fun u1  ->
        fun u2  ->
          fun wl  ->
            let uu____9852 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____9852 with
            | USolved wl1 ->
                let uu____9854 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____9854
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 -> solve env (defer "" orig wl1)
and solve_maybe_uinsts:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> worklist -> univ_eq_sol
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
                  let uu____9900 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____9900 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9903 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9915;
                  FStar_Syntax_Syntax.vars = uu____9916;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9919;
                  FStar_Syntax_Syntax.vars = uu____9920;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9934,uu____9935) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9942,FStar_Syntax_Syntax.Tm_uinst uu____9943) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9950 -> USolved wl
and giveup_or_defer:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> Prims.string -> solution
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____9960 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____9960
              then
                let uu____9961 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9961 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____9970 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____9970
         then
           let uu____9971 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____9971
         else ());
        (let uu____9973 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____9973 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10035 = head_matches_delta env () t1 t2 in
               match uu____10035 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10076 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10125 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10140 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____10141 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____10140, uu____10141)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10146 =
                                FStar_Syntax_Subst.compress t1 in
                              let uu____10147 =
                                FStar_Syntax_Subst.compress t2 in
                              (uu____10146, uu____10147) in
                        (match uu____10125 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10173 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____10173 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10204 =
                                    let uu____10213 =
                                      let uu____10216 =
                                        let uu____10219 =
                                          let uu____10220 =
                                            let uu____10227 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____10227) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10220 in
                                        FStar_Syntax_Syntax.mk uu____10219 in
                                      uu____10216
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____10235 =
                                      let uu____10238 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____10238] in
                                    (uu____10213, uu____10235) in
                                  FStar_Pervasives_Native.Some uu____10204
                              | (uu____10251,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10253)) ->
                                  let uu____10258 =
                                    let uu____10265 =
                                      let uu____10268 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____10268] in
                                    (t11, uu____10265) in
                                  FStar_Pervasives_Native.Some uu____10258
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10278),uu____10279) ->
                                  let uu____10284 =
                                    let uu____10291 =
                                      let uu____10294 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____10294] in
                                    (t21, uu____10291) in
                                  FStar_Pervasives_Native.Some uu____10284
                              | uu____10303 ->
                                  let uu____10308 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____10308 with
                                   | (head1,uu____10332) ->
                                       let uu____10353 =
                                         let uu____10354 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____10354.FStar_Syntax_Syntax.n in
                                       (match uu____10353 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10365;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10367;_}
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
                                                [FStar_TypeChecker_Normalize.WHNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t11 in
                                            let t22 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.WHNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t21 in
                                            disjoin t12 t22
                                        | uu____10374 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10387) ->
                  let uu____10412 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___129_10438  ->
                            match uu___129_10438 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10445 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10445 with
                                      | (u',uu____10461) ->
                                          let uu____10482 =
                                            let uu____10483 = whnf env u' in
                                            uu____10483.FStar_Syntax_Syntax.n in
                                          (match uu____10482 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10487) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10512 -> false))
                                 | uu____10513 -> false)
                            | uu____10516 -> false)) in
                  (match uu____10412 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10550 tps =
                         match uu____10550 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10598 =
                                    let uu____10607 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10607 in
                                  (match uu____10598 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10642 -> FStar_Pervasives_Native.None) in
                       let uu____10651 =
                         let uu____10660 =
                           let uu____10667 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10667, []) in
                         make_lower_bound uu____10660 lower_bounds in
                       (match uu____10651 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10679 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10679
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
                                "meeting refinements" in
                            ((let uu____10699 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10699
                              then
                                let wl' =
                                  let uu___156_10701 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___156_10701.wl_deferred);
                                    ctr = (uu___156_10701.ctr);
                                    defer_ok = (uu___156_10701.defer_ok);
                                    smt_ok = (uu___156_10701.smt_ok);
                                    tcenv = (uu___156_10701.tcenv)
                                  } in
                                let uu____10702 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10702
                              else ());
                             (let uu____10704 =
                                solve_t env eq_prob
                                  (let uu___157_10706 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___157_10706.wl_deferred);
                                     ctr = (uu___157_10706.ctr);
                                     defer_ok = (uu___157_10706.defer_ok);
                                     smt_ok = (uu___157_10706.smt_ok);
                                     tcenv = (uu___157_10706.tcenv)
                                   }) in
                              match uu____10704 with
                              | Success uu____10709 ->
                                  let wl1 =
                                    let uu___158_10711 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___158_10711.wl_deferred);
                                      ctr = (uu___158_10711.ctr);
                                      defer_ok = (uu___158_10711.defer_ok);
                                      smt_ok = (uu___158_10711.smt_ok);
                                      tcenv = (uu___158_10711.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10713 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10718 -> FStar_Pervasives_Native.None))))
              | uu____10719 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10728 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10728
         then
           let uu____10729 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10729
         else ());
        (let uu____10731 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10731 with
         | (u,args) ->
             let uu____10770 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____10770 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____10811 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____10811 with
                    | (h1,args1) ->
                        let uu____10852 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____10852 with
                         | (h2,uu____10872) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10899 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____10899
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____10917 =
                                          let uu____10920 =
                                            let uu____10921 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____10921 in
                                          [uu____10920] in
                                        FStar_Pervasives_Native.Some
                                          uu____10917))
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
                                       (let uu____10954 =
                                          let uu____10957 =
                                            let uu____10958 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____10958 in
                                          [uu____10957] in
                                        FStar_Pervasives_Native.Some
                                          uu____10954))
                                  else FStar_Pervasives_Native.None
                              | uu____10972 -> FStar_Pervasives_Native.None)) in
                  let conjoin t1 t2 =
                    match ((t1.FStar_Syntax_Syntax.n),
                            (t2.FStar_Syntax_Syntax.n))
                    with
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,phi1),FStar_Syntax_Syntax.Tm_refine (y,phi2)) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort
                            y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             let x1 = FStar_Syntax_Syntax.freshen_bv x in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x1)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let uu____11062 =
                               let uu____11071 =
                                 let uu____11074 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____11074 in
                               (uu____11071, m1) in
                             FStar_Pervasives_Native.Some uu____11062)
                    | (uu____11087,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11089)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11137),uu____11138) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11185 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11238) ->
                       let uu____11263 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___130_11289  ->
                                 match uu___130_11289 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11296 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____11296 with
                                           | (u',uu____11312) ->
                                               let uu____11333 =
                                                 let uu____11334 =
                                                   whnf env u' in
                                                 uu____11334.FStar_Syntax_Syntax.n in
                                               (match uu____11333 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11338) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11363 -> false))
                                      | uu____11364 -> false)
                                 | uu____11367 -> false)) in
                       (match uu____11263 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11405 tps =
                              match uu____11405 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11467 =
                                         let uu____11478 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11478 in
                                       (match uu____11467 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11529 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11540 =
                              let uu____11551 =
                                let uu____11560 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11560, []) in
                              make_upper_bound uu____11551 upper_bounds in
                            (match uu____11540 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11574 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11574
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
                                     "joining refinements" in
                                 ((let uu____11600 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11600
                                   then
                                     let wl' =
                                       let uu___159_11602 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___159_11602.wl_deferred);
                                         ctr = (uu___159_11602.ctr);
                                         defer_ok = (uu___159_11602.defer_ok);
                                         smt_ok = (uu___159_11602.smt_ok);
                                         tcenv = (uu___159_11602.tcenv)
                                       } in
                                     let uu____11603 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11603
                                   else ());
                                  (let uu____11605 =
                                     solve_t env eq_prob
                                       (let uu___160_11607 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___160_11607.wl_deferred);
                                          ctr = (uu___160_11607.ctr);
                                          defer_ok =
                                            (uu___160_11607.defer_ok);
                                          smt_ok = (uu___160_11607.smt_ok);
                                          tcenv = (uu___160_11607.tcenv)
                                        }) in
                                   match uu____11605 with
                                   | Success uu____11610 ->
                                       let wl1 =
                                         let uu___161_11612 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___161_11612.wl_deferred);
                                           ctr = (uu___161_11612.ctr);
                                           defer_ok =
                                             (uu___161_11612.defer_ok);
                                           smt_ok = (uu___161_11612.smt_ok);
                                           tcenv = (uu___161_11612.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11614 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11619 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11620 -> failwith "Impossible: Not a flex-rigid")))
and solve_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.prob ->
          worklist ->
            (FStar_Syntax_Syntax.binders ->
               FStar_TypeChecker_Env.env ->
                 FStar_Syntax_Syntax.subst_elt Prims.list ->
                   FStar_TypeChecker_Common.prob)
              -> solution
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
                    let rhs_prob = rhs (FStar_List.rev scope) env1 subst1 in
                    ((let uu____11711 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11711
                      then
                        let uu____11712 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11712
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___162_11766 = hd1 in
                      let uu____11767 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___162_11766.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___162_11766.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11767
                      } in
                    let hd21 =
                      let uu___163_11771 = hd2 in
                      let uu____11772 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___163_11771.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___163_11771.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11772
                      } in
                    let prob =
                      let uu____11776 =
                        let uu____11781 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11781 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____11776 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11792 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11792 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11796 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____11796 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11826 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11831 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11826 uu____11831 in
                         ((let uu____11841 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11841
                           then
                             let uu____11842 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11843 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11842 uu____11843
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11866 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11876 = aux scope env [] bs1 bs2 in
              match uu____11876 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11900 = compress_tprob wl problem in
        solve_t' env uu____11900 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11933 = head_matches_delta env1 wl1 t1 t2 in
          match uu____11933 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____11964,uu____11965) ->
                   let may_relate head3 =
                     let uu____11990 =
                       let uu____11991 = FStar_Syntax_Util.un_uinst head3 in
                       uu____11991.FStar_Syntax_Syntax.n in
                     match uu____11990 with
                     | FStar_Syntax_Syntax.Tm_name uu____11994 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____11995 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____12019 -> false in
                   let uu____12020 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____12020
                   then
                     let guard =
                       if
                         problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ
                       then mk_eq2 env1 t1 t2
                       else
                         (let has_type_guard t11 t21 =
                            match problem.FStar_TypeChecker_Common.element
                            with
                            | FStar_Pervasives_Native.Some t ->
                                FStar_Syntax_Util.mk_has_type t11 t t21
                            | FStar_Pervasives_Native.None  ->
                                let x =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None t11 in
                                let u_x =
                                  env1.FStar_TypeChecker_Env.universe_of env1
                                    t11 in
                                let uu____12037 =
                                  let uu____12038 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____12038 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____12037 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____12040 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____12040
                   else
                     (let uu____12042 =
                        let uu____12043 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____12044 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____12043 uu____12044 in
                      giveup env1 uu____12042 orig)
               | (uu____12045,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___164_12059 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___164_12059.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___164_12059.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___164_12059.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___164_12059.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___164_12059.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___164_12059.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___164_12059.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___164_12059.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____12060,FStar_Pervasives_Native.None ) ->
                   ((let uu____12072 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____12072
                     then
                       let uu____12073 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____12074 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____12075 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____12076 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____12073
                         uu____12074 uu____12075 uu____12076
                     else ());
                    (let uu____12078 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____12078 with
                     | (head11,args1) ->
                         let uu____12115 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____12115 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____12169 =
                                  let uu____12170 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____12171 = args_to_string args1 in
                                  let uu____12172 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____12173 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____12170 uu____12171 uu____12172
                                    uu____12173 in
                                giveup env1 uu____12169 orig
                              else
                                (let uu____12175 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____12181 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____12181 = FStar_Syntax_Util.Equal) in
                                 if uu____12175
                                 then
                                   let uu____12182 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____12182 with
                                   | USolved wl2 ->
                                       let uu____12184 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____12184
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____12188 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____12188 with
                                    | (base1,refinement1) ->
                                        let uu____12225 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____12225 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12306 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____12306 with
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
                                                           (fun uu____12328 
                                                              ->
                                                              fun uu____12329
                                                                 ->
                                                                match 
                                                                  (uu____12328,
                                                                    uu____12329)
                                                                with
                                                                | ((a,uu____12347),
                                                                   (a',uu____12349))
                                                                    ->
                                                                    let uu____12358
                                                                    =
                                                                    mk_problem
                                                                    (p_scope
                                                                    orig)
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index" in
                                                                    FStar_All.pipe_left
                                                                    (fun
                                                                    _0_56  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_56)
                                                                    uu____12358)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____12368 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12368 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12374 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___165_12422 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___165_12422.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___165_12422.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___165_12422.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___165_12422.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___165_12422.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___165_12422.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___165_12422.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___165_12422.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____12442 = p in
          match uu____12442 with
          | (((u,k),xs,c),ps,(h,uu____12453,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____12535 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____12535 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____12558 = h gs_xs in
                     let uu____12559 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57) in
                     FStar_Syntax_Util.abs xs1 uu____12558 uu____12559 in
                   ((let uu____12565 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____12565
                     then
                       let uu____12566 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____12567 = FStar_Syntax_Print.comp_to_string c in
                       let uu____12568 = FStar_Syntax_Print.term_to_string im in
                       let uu____12569 = FStar_Syntax_Print.tag_of_term im in
                       let uu____12570 =
                         let uu____12571 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____12571
                           (FStar_String.concat ", ") in
                       let uu____12576 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____12566 uu____12567 uu____12568 uu____12569
                         uu____12570 uu____12576
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___131_12597 =
          match uu___131_12597 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____12629 = p in
          match uu____12629 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____12720 = FStar_List.nth ps i in
              (match uu____12720 with
               | (pi,uu____12724) ->
                   let uu____12729 = FStar_List.nth xs i in
                   (match uu____12729 with
                    | (xi,uu____12741) ->
                        let rec gs k =
                          let uu____12754 = FStar_Syntax_Util.arrow_formals k in
                          match uu____12754 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____12841)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____12854 = new_uvar r xs k_a in
                                    (match uu____12854 with
                                     | (gi_xs,gi) ->
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
                                         let uu____12876 = aux subst2 tl1 in
                                         (match uu____12876 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____12903 =
                                                let uu____12906 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____12906 :: gi_xs' in
                                              let uu____12907 =
                                                let uu____12910 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____12910 :: gi_ps' in
                                              (uu____12903, uu____12907))) in
                              aux [] bs in
                        let uu____12915 =
                          let uu____12916 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____12916 in
                        if uu____12915
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____12920 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____12920 with
                           | (g_xs,uu____12932) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____12943 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____12944 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58) in
                                 FStar_Syntax_Util.abs xs uu____12943
                                   uu____12944 in
                               let sub1 =
                                 let uu____12950 =
                                   let uu____12955 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____12958 =
                                     let uu____12961 =
                                       FStar_List.map
                                         (fun uu____12976  ->
                                            match uu____12976 with
                                            | (uu____12985,uu____12986,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____12961 in
                                   mk_problem (p_scope orig) orig uu____12955
                                     (p_rel orig) uu____12958
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____12950 in
                               ((let uu____13001 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____13001
                                 then
                                   let uu____13002 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____13003 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____13002 uu____13003
                                 else ());
                                (let wl2 =
                                   let uu____13006 =
                                     let uu____13009 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____13009 in
                                   solve_prob orig uu____13006
                                     [TERM (u, proj)] wl1 in
                                 let uu____13018 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____13018))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____13049 = lhs in
          match uu____13049 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____13085 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____13085 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____13118 =
                        let uu____13165 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____13165) in
                      FStar_Pervasives_Native.Some uu____13118
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____13309 =
                           let uu____13316 =
                             let uu____13317 = FStar_Syntax_Subst.compress k in
                             uu____13317.FStar_Syntax_Syntax.n in
                           (uu____13316, args) in
                         match uu____13309 with
                         | (uu____13328,[]) ->
                             let uu____13331 =
                               let uu____13342 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____13342) in
                             FStar_Pervasives_Native.Some uu____13331
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____13363,uu____13364) ->
                             let uu____13385 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____13385 with
                              | (uv1,uv_args) ->
                                  let uu____13428 =
                                    let uu____13429 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____13429.FStar_Syntax_Syntax.n in
                                  (match uu____13428 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____13439) ->
                                       let uu____13464 =
                                         pat_vars env [] uv_args in
                                       (match uu____13464 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____13491  ->
                                                      let uu____13492 =
                                                        let uu____13493 =
                                                          let uu____13494 =
                                                            let uu____13499 =
                                                              let uu____13500
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____13500
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____13499 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____13494 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____13493 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____13492)) in
                                            let c1 =
                                              let uu____13510 =
                                                let uu____13511 =
                                                  let uu____13516 =
                                                    let uu____13517 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____13517
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____13516 in
                                                FStar_Pervasives_Native.fst
                                                  uu____13511 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____13510 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____13530 =
                                                let uu____13533 =
                                                  let uu____13534 =
                                                    let uu____13537 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____13537
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____13534 in
                                                FStar_Pervasives_Native.Some
                                                  uu____13533 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____13530 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____13555 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____13560,uu____13561) ->
                             let uu____13580 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____13580 with
                              | (uv1,uv_args) ->
                                  let uu____13623 =
                                    let uu____13624 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____13624.FStar_Syntax_Syntax.n in
                                  (match uu____13623 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____13634) ->
                                       let uu____13659 =
                                         pat_vars env [] uv_args in
                                       (match uu____13659 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____13686  ->
                                                      let uu____13687 =
                                                        let uu____13688 =
                                                          let uu____13689 =
                                                            let uu____13694 =
                                                              let uu____13695
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____13695
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____13694 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____13689 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____13688 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____13687)) in
                                            let c1 =
                                              let uu____13705 =
                                                let uu____13706 =
                                                  let uu____13711 =
                                                    let uu____13712 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____13712
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____13711 in
                                                FStar_Pervasives_Native.fst
                                                  uu____13706 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____13705 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____13725 =
                                                let uu____13728 =
                                                  let uu____13729 =
                                                    let uu____13732 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____13732
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____13729 in
                                                FStar_Pervasives_Native.Some
                                                  uu____13728 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____13725 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____13750 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____13757) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____13798 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____13798
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____13834 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____13834 with
                                  | (args1,rest) ->
                                      let uu____13863 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____13863 with
                                       | (xs2,c2) ->
                                           let uu____13876 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____13876
                                             (fun uu____13900  ->
                                                match uu____13900 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____13940 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____13940 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____14008 =
                                        let uu____14013 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____14013 in
                                      FStar_All.pipe_right uu____14008
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____14028 ->
                             let uu____14035 =
                               let uu____14036 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____14037 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____14038 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____14036 uu____14037 uu____14038 in
                             failwith uu____14035 in
                       let uu____14045 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____14045
                         (fun uu____14100  ->
                            match uu____14100 with
                            | (xs1,c1) ->
                                let uu____14149 =
                                  let uu____14190 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____14190) in
                                FStar_Pervasives_Native.Some uu____14149)) in
              let rec imitate_or_project n1 stopt i =
                if (i >= n1) || (FStar_Option.isNone stopt)
                then
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig
                else
                  (let st = FStar_Option.get stopt in
                   let tx = FStar_Syntax_Unionfind.new_transaction () in
                   if i = (- (Prims.parse_int "1"))
                   then
                     let uu____14308 = imitate orig env wl1 st in
                     match uu____14308 with
                     | Failed uu____14313 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____14321 = project orig env wl1 i st in
                      match uu____14321 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____14329) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____14347 = FStar_Syntax_Util.head_and_args t21 in
                match uu____14347 with
                | (hd1,uu____14363) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____14384 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____14397 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____14398 -> true
                     | uu____14415 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____14419 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____14419
                         then true
                         else
                           ((let uu____14422 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____14422
                             then
                               let uu____14423 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____14423
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____14432 =
                    let uu____14435 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____14435
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____14432 FStar_Syntax_Free.names in
                let uu____14480 = FStar_Util.set_is_empty fvs_hd in
                if uu____14480
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____14491 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____14491 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____14504 =
                            let uu____14505 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____14505 in
                          giveup_or_defer1 orig uu____14504
                        else
                          (let uu____14507 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____14507
                           then
                             let uu____14508 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____14508
                              then
                                let uu____14509 = subterms args_lhs in
                                imitate' orig env wl1 uu____14509
                              else
                                ((let uu____14514 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____14514
                                  then
                                    let uu____14515 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____14516 = names_to_string fvs1 in
                                    let uu____14517 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____14515 uu____14516 uu____14517
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____14524 ->
                                        let uu____14525 = sn_binders env vars in
                                        u_abs k_uv uu____14525 t21 in
                                  let wl2 =
                                    solve_prob orig
                                      FStar_Pervasives_Native.None
                                      [TERM ((uv, k_uv), sol)] wl1 in
                                  solve env wl2)))
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
                               (let uu____14539 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____14539
                                then
                                  ((let uu____14541 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____14541
                                    then
                                      let uu____14542 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____14543 = names_to_string fvs1 in
                                      let uu____14544 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____14542 uu____14543 uu____14544
                                    else ());
                                   (let uu____14546 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs)
                                      uu____14546 (- (Prims.parse_int "1"))))
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
                     (let uu____14557 =
                        let uu____14558 = FStar_Syntax_Free.names t1 in
                        check_head uu____14558 t2 in
                      if uu____14557
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____14563 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____14563
                          then
                            let uu____14564 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____14564
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____14567 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____14567 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____14622 =
               match uu____14622 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k in
                   let uu____14672 = FStar_Syntax_Util.arrow_formals k1 in
                   (match uu____14672 with
                    | (all_formals,uu____14690) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____14853  ->
                                        match uu____14853 with
                                        | (x,imp) ->
                                            let uu____14864 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____14864, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____14877 = FStar_Syntax_Util.type_u () in
                                match uu____14877 with
                                | (t1,uu____14883) ->
                                    let uu____14884 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    FStar_Pervasives_Native.fst uu____14884 in
                              let uu____14889 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____14889 with
                               | (t',tm_u1) ->
                                   let uu____14900 = destruct_flex_t t' in
                                   (match uu____14900 with
                                    | (uu____14935,u1,k11,uu____14938) ->
                                        let sol =
                                          let uu____14984 =
                                            let uu____14993 =
                                              u_abs k1 all_formals t' in
                                            ((u, k1), uu____14993) in
                                          TERM uu____14984 in
                                        let t_app =
                                          FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                            pat_args1
                                            FStar_Pervasives_Native.None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____15093 = pat_var_opt env pat_args hd1 in
                              (match uu____15093 with
                               | FStar_Pervasives_Native.None  ->
                                   aux pat_args pattern_vars pattern_var_set
                                     formals1 tl1
                               | FStar_Pervasives_Native.Some y ->
                                   let maybe_pat =
                                     match xs_opt with
                                     | FStar_Pervasives_Native.None  -> true
                                     | FStar_Pervasives_Native.Some xs ->
                                         FStar_All.pipe_right xs
                                           (FStar_Util.for_some
                                              (fun uu____15150  ->
                                                 match uu____15150 with
                                                 | (x,uu____15156) ->
                                                     FStar_Syntax_Syntax.bv_eq
                                                       x
                                                       (FStar_Pervasives_Native.fst
                                                          y))) in
                                   if Prims.op_Negation maybe_pat
                                   then
                                     aux pat_args pattern_vars
                                       pattern_var_set formals1 tl1
                                   else
                                     (let fvs =
                                        FStar_Syntax_Free.names
                                          (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort in
                                      let uu____15165 =
                                        let uu____15166 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____15166 in
                                      if uu____15165
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____15172 =
                                           FStar_Util.set_add
                                             (FStar_Pervasives_Native.fst
                                                formal) pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____15172 formals1
                                           tl1)))
                          | uu____15183 -> failwith "Impossible" in
                        let uu____15204 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____15204 all_formals args) in
             let solve_both_pats wl1 uu____15269 uu____15270 r =
               match (uu____15269, uu____15270) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15468 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15468
                   then
                     let uu____15469 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15469
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15493 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15493
                       then
                         let uu____15494 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15495 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15496 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15497 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15498 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15494 uu____15495 uu____15496 uu____15497
                           uu____15498
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____15558 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____15558 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____15572 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____15572 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____15626 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____15626 in
                                  let uu____15629 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____15629 k3)
                           else
                             (let uu____15633 =
                                let uu____15634 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____15635 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____15636 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____15634 uu____15635 uu____15636 in
                              failwith uu____15633) in
                       let uu____15637 =
                         let uu____15646 =
                           let uu____15659 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____15659 in
                         match uu____15646 with
                         | (bs,k1') ->
                             let uu____15686 =
                               let uu____15699 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____15699 in
                             (match uu____15686 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____15729 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____15729 in
                                  let uu____15738 =
                                    let uu____15743 =
                                      let uu____15744 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____15744.FStar_Syntax_Syntax.n in
                                    let uu____15747 =
                                      let uu____15748 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____15748.FStar_Syntax_Syntax.n in
                                    (uu____15743, uu____15747) in
                                  (match uu____15738 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____15759,uu____15760) ->
                                       (k1', [sub_prob])
                                   | (uu____15765,FStar_Syntax_Syntax.Tm_type
                                      uu____15766) -> (k2', [sub_prob])
                                   | uu____15771 ->
                                       let uu____15776 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____15776 with
                                        | (t,uu____15790) ->
                                            let uu____15791 = new_uvar r zs t in
                                            (match uu____15791 with
                                             | (k_zs,uu____15805) ->
                                                 let kprob =
                                                   let uu____15807 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs
                                                       FStar_Pervasives_Native.None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_64  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_64) uu____15807 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____15637 with
                       | (k_u',sub_probs) ->
                           let uu____15828 =
                             let uu____15839 =
                               let uu____15840 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____15840 in
                             let uu____15849 =
                               let uu____15852 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____15852 in
                             let uu____15855 =
                               let uu____15858 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____15858 in
                             (uu____15839, uu____15849, uu____15855) in
                           (match uu____15828 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____15877 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____15877 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____15896 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____15896
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____15900 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____15900 with
                                           | (occurs_ok1,msg1) ->
                                               if
                                                 Prims.op_Negation occurs_ok1
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
             let solve_one_pat uu____15953 uu____15954 =
               match (uu____15953, uu____15954) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16072 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____16072
                     then
                       let uu____16073 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____16074 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16073 uu____16074
                     else ());
                    (let uu____16076 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____16076
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16095  ->
                              fun uu____16096  ->
                                match (uu____16095, uu____16096) with
                                | ((a,uu____16114),(t21,uu____16116)) ->
                                    let uu____16125 =
                                      let uu____16130 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16130
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16125
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2 in
                       let guard =
                         let uu____16136 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16136 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16151 = occurs_check env wl (u1, k1) t21 in
                        match uu____16151 with
                        | (occurs_ok,uu____16159) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16167 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16167
                            then
                              let sol =
                                let uu____16169 =
                                  let uu____16178 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16178) in
                                TERM uu____16169 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16185 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16185
                               then
                                 let uu____16186 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16186 with
                                 | (sol,(uu____16204,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16218 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16218
                                       then
                                         let uu____16219 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16219
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16226 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16228 = lhs in
             match uu____16228 with
             | (t1,u1,k1,args1) ->
                 let uu____16233 = rhs in
                 (match uu____16233 with
                  | (t2,u2,k2,args2) ->
                      let maybe_pat_vars1 = pat_vars env [] args1 in
                      let maybe_pat_vars2 = pat_vars env [] args2 in
                      let r = t2.FStar_Syntax_Syntax.pos in
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
                       | uu____16273 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16283 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16283 with
                              | (sol,uu____16295) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16298 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16298
                                    then
                                      let uu____16299 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16299
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16306 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16308 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16308
        then
          let uu____16309 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16309
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16313 = FStar_Util.physical_equality t1 t2 in
           if uu____16313
           then
             let uu____16314 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16314
           else
             ((let uu____16317 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16317
               then
                 let uu____16318 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16318
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____16321,uu____16322) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16323,FStar_Syntax_Syntax.Tm_bvar uu____16324) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___132_16379 =
                     match uu___132_16379 with
                     | [] -> c
                     | bs ->
                         let uu____16401 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16401 in
                   let uu____16410 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16410 with
                    | ((bs11,c11),(bs21,c21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let c12 =
                                   FStar_Syntax_Subst.subst_comp subst1 c11 in
                                 let c22 =
                                   FStar_Syntax_Subst.subst_comp subst1 c21 in
                                 let rel =
                                   let uu____16552 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____16552
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____16554 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____16554))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___133_16630 =
                     match uu___133_16630 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____16664 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____16664 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____16800 =
                                   let uu____16805 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____16806 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____16805
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____16806 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____16800))
               | (FStar_Syntax_Syntax.Tm_abs uu____16811,uu____16812) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____16837 -> true
                     | uu____16854 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____16888 =
                     let uu____16905 = maybe_eta t1 in
                     let uu____16912 = maybe_eta t2 in
                     (uu____16905, uu____16912) in
                   (match uu____16888 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_16954 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_16954.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_16954.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_16954.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_16954.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_16954.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_16954.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_16954.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_16954.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____16977 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____16977
                        then
                          let uu____16978 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____16978 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17006 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17006
                        then
                          let uu____17007 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17007 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____17015 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17032,FStar_Syntax_Syntax.Tm_abs uu____17033) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17058 -> true
                     | uu____17075 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____17109 =
                     let uu____17126 = maybe_eta t1 in
                     let uu____17133 = maybe_eta t2 in
                     (uu____17126, uu____17133) in
                   (match uu____17109 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_17175 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_17175.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_17175.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_17175.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_17175.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_17175.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_17175.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_17175.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_17175.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17198 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17198
                        then
                          let uu____17199 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17199 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17227 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17227
                        then
                          let uu____17228 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17228 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____17236 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____17253,FStar_Syntax_Syntax.Tm_refine uu____17254) ->
                   let uu____17267 = as_refinement env wl t1 in
                   (match uu____17267 with
                    | (x1,phi1) ->
                        let uu____17274 = as_refinement env wl t2 in
                        (match uu____17274 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____17282 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____17282 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____17320 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____17320
                                 (guard_on_element wl problem x11) in
                             let fallback uu____17324 =
                               let impl =
                                 if
                                   problem.FStar_TypeChecker_Common.relation
                                     = FStar_TypeChecker_Common.EQ
                                 then
                                   mk_imp1 FStar_Syntax_Util.mk_iff phi11
                                     phi21
                                 else
                                   mk_imp1 FStar_Syntax_Util.mk_imp phi11
                                     phi21 in
                               let guard =
                                 let uu____17330 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____17330 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____17339 =
                                   let uu____17344 =
                                     let uu____17345 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____17345 :: (p_scope orig) in
                                   mk_problem uu____17344 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____17339 in
                               let uu____17350 =
                                 solve env1
                                   (let uu___167_17352 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___167_17352.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___167_17352.smt_ok);
                                      tcenv = (uu___167_17352.tcenv)
                                    }) in
                               (match uu____17350 with
                                | Failed uu____17359 -> fallback ()
                                | Success uu____17364 ->
                                    let guard =
                                      let uu____17368 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____17373 =
                                        let uu____17374 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____17374
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____17368
                                        uu____17373 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___168_17383 = wl1 in
                                      {
                                        attempting =
                                          (uu___168_17383.attempting);
                                        wl_deferred =
                                          (uu___168_17383.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___168_17383.defer_ok);
                                        smt_ok = (uu___168_17383.smt_ok);
                                        tcenv = (uu___168_17383.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17385,FStar_Syntax_Syntax.Tm_uvar uu____17386) ->
                   let uu____17419 = destruct_flex_t t1 in
                   let uu____17420 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17419 uu____17420
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17421;
                     FStar_Syntax_Syntax.pos = uu____17422;
                     FStar_Syntax_Syntax.vars = uu____17423;_},uu____17424),FStar_Syntax_Syntax.Tm_uvar
                  uu____17425) ->
                   let uu____17478 = destruct_flex_t t1 in
                   let uu____17479 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17478 uu____17479
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17480,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17481;
                     FStar_Syntax_Syntax.pos = uu____17482;
                     FStar_Syntax_Syntax.vars = uu____17483;_},uu____17484))
                   ->
                   let uu____17537 = destruct_flex_t t1 in
                   let uu____17538 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17537 uu____17538
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17539;
                     FStar_Syntax_Syntax.pos = uu____17540;
                     FStar_Syntax_Syntax.vars = uu____17541;_},uu____17542),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17543;
                     FStar_Syntax_Syntax.pos = uu____17544;
                     FStar_Syntax_Syntax.vars = uu____17545;_},uu____17546))
                   ->
                   let uu____17619 = destruct_flex_t t1 in
                   let uu____17620 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17619 uu____17620
               | (FStar_Syntax_Syntax.Tm_uvar uu____17621,uu____17622) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____17639 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____17639 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17646;
                     FStar_Syntax_Syntax.pos = uu____17647;
                     FStar_Syntax_Syntax.vars = uu____17648;_},uu____17649),uu____17650)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____17687 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____17687 t2 wl
               | (uu____17694,FStar_Syntax_Syntax.Tm_uvar uu____17695) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____17712,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17713;
                     FStar_Syntax_Syntax.pos = uu____17714;
                     FStar_Syntax_Syntax.vars = uu____17715;_},uu____17716))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17753,FStar_Syntax_Syntax.Tm_type uu____17754) ->
                   solve_t' env
                     (let uu___169_17772 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_17772.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_17772.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_17772.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_17772.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_17772.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_17772.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_17772.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_17772.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_17772.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17773;
                     FStar_Syntax_Syntax.pos = uu____17774;
                     FStar_Syntax_Syntax.vars = uu____17775;_},uu____17776),FStar_Syntax_Syntax.Tm_type
                  uu____17777) ->
                   solve_t' env
                     (let uu___169_17815 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_17815.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_17815.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_17815.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_17815.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_17815.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_17815.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_17815.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_17815.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_17815.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17816,FStar_Syntax_Syntax.Tm_arrow uu____17817) ->
                   solve_t' env
                     (let uu___169_17847 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_17847.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_17847.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_17847.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_17847.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_17847.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_17847.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_17847.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_17847.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_17847.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17848;
                     FStar_Syntax_Syntax.pos = uu____17849;
                     FStar_Syntax_Syntax.vars = uu____17850;_},uu____17851),FStar_Syntax_Syntax.Tm_arrow
                  uu____17852) ->
                   solve_t' env
                     (let uu___169_17902 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_17902.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_17902.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_17902.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_17902.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_17902.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_17902.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_17902.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_17902.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_17902.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____17903,uu____17904) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____17923 =
                        let uu____17924 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____17924 in
                      if uu____17923
                      then
                        let uu____17925 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___170_17931 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_17931.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_17931.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_17931.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_17931.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_17931.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_17931.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_17931.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_17931.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_17931.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____17932 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____17925 uu____17932 t2
                          wl
                      else
                        (let uu____17940 = base_and_refinement env wl t2 in
                         match uu____17940 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____17983 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___171_17989 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_17989.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_17989.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_17989.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_17989.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_17989.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_17989.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_17989.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_17989.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_17989.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____17990 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____17983
                                    uu____17990 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___172_18010 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_18010.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_18010.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18013 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____18013 in
                                  let guard =
                                    let uu____18025 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18025
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18033;
                     FStar_Syntax_Syntax.pos = uu____18034;
                     FStar_Syntax_Syntax.vars = uu____18035;_},uu____18036),uu____18037)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18076 =
                        let uu____18077 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18077 in
                      if uu____18076
                      then
                        let uu____18078 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___170_18084 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_18084.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_18084.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_18084.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_18084.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_18084.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_18084.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_18084.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_18084.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_18084.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18085 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18078 uu____18085 t2
                          wl
                      else
                        (let uu____18093 = base_and_refinement env wl t2 in
                         match uu____18093 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18136 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___171_18142 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_18142.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_18142.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_18142.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_18142.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_18142.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_18142.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_18142.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_18142.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_18142.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18143 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18136
                                    uu____18143 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___172_18163 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_18163.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_18163.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18166 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____18166 in
                                  let guard =
                                    let uu____18178 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18178
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18186,FStar_Syntax_Syntax.Tm_uvar uu____18187) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18205 = base_and_refinement env wl t1 in
                      match uu____18205 with
                      | (t_base,uu____18221) ->
                          solve_t env
                            (let uu___173_18243 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_18243.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_18243.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_18243.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_18243.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_18243.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_18243.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_18243.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_18243.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18246,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18247;
                     FStar_Syntax_Syntax.pos = uu____18248;
                     FStar_Syntax_Syntax.vars = uu____18249;_},uu____18250))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18288 = base_and_refinement env wl t1 in
                      match uu____18288 with
                      | (t_base,uu____18304) ->
                          solve_t env
                            (let uu___173_18326 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_18326.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_18326.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_18326.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_18326.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_18326.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_18326.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_18326.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_18326.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18329,uu____18330) ->
                   let t21 =
                     let uu____18340 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____18340 in
                   solve_t env
                     (let uu___174_18364 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_18364.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___174_18364.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___174_18364.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___174_18364.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_18364.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_18364.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_18364.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_18364.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_18364.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____18365,FStar_Syntax_Syntax.Tm_refine uu____18366) ->
                   let t11 =
                     let uu____18376 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____18376 in
                   solve_t env
                     (let uu___175_18400 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_18400.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_18400.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_18400.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_18400.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_18400.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_18400.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_18400.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_18400.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_18400.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____18403,uu____18404) ->
                   let head1 =
                     let uu____18430 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18430
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18474 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18474
                       FStar_Pervasives_Native.fst in
                   let uu____18515 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18515
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18530 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18530
                      then
                        let guard =
                          let uu____18542 =
                            let uu____18543 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18543 = FStar_Syntax_Util.Equal in
                          if uu____18542
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18547 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____18547) in
                        let uu____18550 = solve_prob orig guard [] wl in
                        solve env uu____18550
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____18553,uu____18554) ->
                   let head1 =
                     let uu____18564 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18564
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18608 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18608
                       FStar_Pervasives_Native.fst in
                   let uu____18649 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18649
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18664 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18664
                      then
                        let guard =
                          let uu____18676 =
                            let uu____18677 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18677 = FStar_Syntax_Util.Equal in
                          if uu____18676
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18681 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____18681) in
                        let uu____18684 = solve_prob orig guard [] wl in
                        solve env uu____18684
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____18687,uu____18688) ->
                   let head1 =
                     let uu____18692 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18692
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18736 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18736
                       FStar_Pervasives_Native.fst in
                   let uu____18777 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18777
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18792 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18792
                      then
                        let guard =
                          let uu____18804 =
                            let uu____18805 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18805 = FStar_Syntax_Util.Equal in
                          if uu____18804
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18809 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____18809) in
                        let uu____18812 = solve_prob orig guard [] wl in
                        solve env uu____18812
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____18815,uu____18816) ->
                   let head1 =
                     let uu____18820 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18820
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18864 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18864
                       FStar_Pervasives_Native.fst in
                   let uu____18905 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18905
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18920 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18920
                      then
                        let guard =
                          let uu____18932 =
                            let uu____18933 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18933 = FStar_Syntax_Util.Equal in
                          if uu____18932
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18937 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____18937) in
                        let uu____18940 = solve_prob orig guard [] wl in
                        solve env uu____18940
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____18943,uu____18944) ->
                   let head1 =
                     let uu____18948 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18948
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18992 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18992
                       FStar_Pervasives_Native.fst in
                   let uu____19033 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19033
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19048 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19048
                      then
                        let guard =
                          let uu____19060 =
                            let uu____19061 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19061 = FStar_Syntax_Util.Equal in
                          if uu____19060
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19065 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19065) in
                        let uu____19068 = solve_prob orig guard [] wl in
                        solve env uu____19068
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19071,uu____19072) ->
                   let head1 =
                     let uu____19090 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19090
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19134 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19134
                       FStar_Pervasives_Native.fst in
                   let uu____19175 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19175
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19190 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19190
                      then
                        let guard =
                          let uu____19202 =
                            let uu____19203 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19203 = FStar_Syntax_Util.Equal in
                          if uu____19202
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19207 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19207) in
                        let uu____19210 = solve_prob orig guard [] wl in
                        solve env uu____19210
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19213,FStar_Syntax_Syntax.Tm_match uu____19214) ->
                   let head1 =
                     let uu____19240 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19240
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19284 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19284
                       FStar_Pervasives_Native.fst in
                   let uu____19325 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19325
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19340 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19340
                      then
                        let guard =
                          let uu____19352 =
                            let uu____19353 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19353 = FStar_Syntax_Util.Equal in
                          if uu____19352
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19357 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19357) in
                        let uu____19360 = solve_prob orig guard [] wl in
                        solve env uu____19360
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19363,FStar_Syntax_Syntax.Tm_uinst uu____19364) ->
                   let head1 =
                     let uu____19374 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19374
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19418 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19418
                       FStar_Pervasives_Native.fst in
                   let uu____19459 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19459
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19474 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19474
                      then
                        let guard =
                          let uu____19486 =
                            let uu____19487 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19487 = FStar_Syntax_Util.Equal in
                          if uu____19486
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19491 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____19491) in
                        let uu____19494 = solve_prob orig guard [] wl in
                        solve env uu____19494
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19497,FStar_Syntax_Syntax.Tm_name uu____19498) ->
                   let head1 =
                     let uu____19502 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19502
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19546 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19546
                       FStar_Pervasives_Native.fst in
                   let uu____19587 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19587
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19602 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19602
                      then
                        let guard =
                          let uu____19614 =
                            let uu____19615 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19615 = FStar_Syntax_Util.Equal in
                          if uu____19614
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19619 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____19619) in
                        let uu____19622 = solve_prob orig guard [] wl in
                        solve env uu____19622
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19625,FStar_Syntax_Syntax.Tm_constant uu____19626) ->
                   let head1 =
                     let uu____19630 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19630
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19674 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19674
                       FStar_Pervasives_Native.fst in
                   let uu____19715 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19715
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19730 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19730
                      then
                        let guard =
                          let uu____19742 =
                            let uu____19743 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19743 = FStar_Syntax_Util.Equal in
                          if uu____19742
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19747 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____19747) in
                        let uu____19750 = solve_prob orig guard [] wl in
                        solve env uu____19750
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19753,FStar_Syntax_Syntax.Tm_fvar uu____19754) ->
                   let head1 =
                     let uu____19758 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19758
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19802 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19802
                       FStar_Pervasives_Native.fst in
                   let uu____19843 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19843
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19858 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19858
                      then
                        let guard =
                          let uu____19870 =
                            let uu____19871 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19871 = FStar_Syntax_Util.Equal in
                          if uu____19870
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19875 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____19875) in
                        let uu____19878 = solve_prob orig guard [] wl in
                        solve env uu____19878
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19881,FStar_Syntax_Syntax.Tm_app uu____19882) ->
                   let head1 =
                     let uu____19900 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19900
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19944 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19944
                       FStar_Pervasives_Native.fst in
                   let uu____19985 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19985
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20000 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20000
                      then
                        let guard =
                          let uu____20012 =
                            let uu____20013 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20013 = FStar_Syntax_Util.Equal in
                          if uu____20012
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20017 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20017) in
                        let uu____20020 = solve_prob orig guard [] wl in
                        solve env uu____20020
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____20024,uu____20025),uu____20026) ->
                   solve_t' env
                     (let uu___176_20068 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_20068.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___176_20068.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___176_20068.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___176_20068.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_20068.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_20068.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_20068.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_20068.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_20068.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____20071,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____20073,uu____20074)) ->
                   solve_t' env
                     (let uu___177_20116 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___177_20116.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___177_20116.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___177_20116.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___177_20116.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___177_20116.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___177_20116.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___177_20116.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___177_20116.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___177_20116.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____20117,uu____20118) ->
                   let uu____20131 =
                     let uu____20132 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20133 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20132
                       uu____20133 in
                   failwith uu____20131
               | (FStar_Syntax_Syntax.Tm_meta uu____20134,uu____20135) ->
                   let uu____20142 =
                     let uu____20143 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20144 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20143
                       uu____20144 in
                   failwith uu____20142
               | (FStar_Syntax_Syntax.Tm_delayed uu____20145,uu____20146) ->
                   let uu____20171 =
                     let uu____20172 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20173 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20172
                       uu____20173 in
                   failwith uu____20171
               | (uu____20174,FStar_Syntax_Syntax.Tm_meta uu____20175) ->
                   let uu____20182 =
                     let uu____20183 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20184 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20183
                       uu____20184 in
                   failwith uu____20182
               | (uu____20185,FStar_Syntax_Syntax.Tm_delayed uu____20186) ->
                   let uu____20211 =
                     let uu____20212 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20213 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20212
                       uu____20213 in
                   failwith uu____20211
               | (uu____20214,FStar_Syntax_Syntax.Tm_let uu____20215) ->
                   let uu____20228 =
                     let uu____20229 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20230 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20229
                       uu____20230 in
                   failwith uu____20228
               | uu____20231 -> giveup env "head tag mismatch" orig)))
and solve_c:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem ->
      worklist -> solution
  =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let c1 = problem.FStar_TypeChecker_Common.lhs in
        let c2 = problem.FStar_TypeChecker_Common.rhs in
        let orig = FStar_TypeChecker_Common.CProb problem in
        let sub_prob t1 rel t2 reason =
          mk_problem (p_scope orig) orig t1 rel t2
            FStar_Pervasives_Native.None reason in
        let solve_eq c1_comp c2_comp =
          (let uu____20267 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20267
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____20287  ->
                  fun uu____20288  ->
                    match (uu____20287, uu____20288) with
                    | ((a1,uu____20306),(a2,uu____20308)) ->
                        let uu____20317 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_88  -> FStar_TypeChecker_Common.TProb _0_88)
                          uu____20317)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____20327 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p)
                      FStar_Pervasives_Native.fst) sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____20327 in
           let wl1 =
             solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20351 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20358)::[] -> wp1
              | uu____20375 ->
                  let uu____20384 =
                    let uu____20385 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20385 in
                  failwith uu____20384 in
            let uu____20388 =
              let uu____20397 =
                let uu____20398 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20398 in
              [uu____20397] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20388;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20399 = lift_c1 () in solve_eq uu____20399 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___134_20405  ->
                       match uu___134_20405 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20406 -> false)) in
             let uu____20407 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20441)::uu____20442,(wp2,uu____20444)::uu____20445)
                   -> (wp1, wp2)
               | uu____20502 ->
                   let uu____20523 =
                     let uu____20524 =
                       let uu____20529 =
                         let uu____20530 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____20531 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____20530 uu____20531 in
                       (uu____20529, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____20524 in
                   FStar_Exn.raise uu____20523 in
             match uu____20407 with
             | (wpc1,wpc2) ->
                 let uu____20550 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____20550
                 then
                   let uu____20553 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____20553 wl
                 else
                   (let uu____20557 =
                      let uu____20564 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____20564 in
                    match uu____20557 with
                    | (c2_decl,qualifiers) ->
                        let uu____20585 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____20585
                        then
                          let c1_repr =
                            let uu____20589 =
                              let uu____20590 =
                                let uu____20591 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____20591 in
                              let uu____20592 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20590 uu____20592 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____20589 in
                          let c2_repr =
                            let uu____20594 =
                              let uu____20595 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____20596 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20595 uu____20596 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____20594 in
                          let prob =
                            let uu____20598 =
                              let uu____20603 =
                                let uu____20604 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____20605 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____20604
                                  uu____20605 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____20603 in
                            FStar_TypeChecker_Common.TProb uu____20598 in
                          let wl1 =
                            let uu____20607 =
                              let uu____20610 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____20610 in
                            solve_prob orig uu____20607 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____20619 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____20619
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____20621 =
                                     let uu____20624 =
                                       let uu____20625 =
                                         let uu____20640 =
                                           let uu____20641 =
                                             let uu____20642 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____20642] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____20641 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____20643 =
                                           let uu____20646 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____20647 =
                                             let uu____20650 =
                                               let uu____20651 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20651 in
                                             [uu____20650] in
                                           uu____20646 :: uu____20647 in
                                         (uu____20640, uu____20643) in
                                       FStar_Syntax_Syntax.Tm_app uu____20625 in
                                     FStar_Syntax_Syntax.mk uu____20624 in
                                   uu____20621 FStar_Pervasives_Native.None r))
                               else
                                 (let uu____20658 =
                                    let uu____20661 =
                                      let uu____20662 =
                                        let uu____20677 =
                                          let uu____20678 =
                                            let uu____20679 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____20679] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____20678 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____20680 =
                                          let uu____20683 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____20684 =
                                            let uu____20687 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____20688 =
                                              let uu____20691 =
                                                let uu____20692 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20692 in
                                              [uu____20691] in
                                            uu____20687 :: uu____20688 in
                                          uu____20683 :: uu____20684 in
                                        (uu____20677, uu____20680) in
                                      FStar_Syntax_Syntax.Tm_app uu____20662 in
                                    FStar_Syntax_Syntax.mk uu____20661 in
                                  uu____20658 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____20699 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____20699 in
                           let wl1 =
                             let uu____20709 =
                               let uu____20712 =
                                 let uu____20715 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____20715 g in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____20712 in
                             solve_prob orig uu____20709 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____20728 = FStar_Util.physical_equality c1 c2 in
        if uu____20728
        then
          let uu____20729 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____20729
        else
          ((let uu____20732 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____20732
            then
              let uu____20733 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____20734 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20733
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20734
            else ());
           (let uu____20736 =
              let uu____20741 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____20742 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____20741, uu____20742) in
            match uu____20736 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20746),FStar_Syntax_Syntax.Total
                    (t2,uu____20748)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____20765 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20765 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20768,FStar_Syntax_Syntax.Total uu____20769) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20787),FStar_Syntax_Syntax.Total
                    (t2,uu____20789)) ->
                     let uu____20806 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20806 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20810),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20812)) ->
                     let uu____20829 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20829 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20833),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20835)) ->
                     let uu____20852 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20852 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20855,FStar_Syntax_Syntax.Comp uu____20856) ->
                     let uu____20865 =
                       let uu___178_20870 = problem in
                       let uu____20875 =
                         let uu____20876 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20876 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_20870.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20875;
                         FStar_TypeChecker_Common.relation =
                           (uu___178_20870.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___178_20870.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___178_20870.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_20870.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_20870.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_20870.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_20870.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_20870.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20865 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____20877,FStar_Syntax_Syntax.Comp uu____20878) ->
                     let uu____20887 =
                       let uu___178_20892 = problem in
                       let uu____20897 =
                         let uu____20898 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20898 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_20892.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20897;
                         FStar_TypeChecker_Common.relation =
                           (uu___178_20892.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___178_20892.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___178_20892.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_20892.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_20892.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_20892.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_20892.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_20892.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20887 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20899,FStar_Syntax_Syntax.GTotal uu____20900) ->
                     let uu____20909 =
                       let uu___179_20914 = problem in
                       let uu____20919 =
                         let uu____20920 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20920 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_20914.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___179_20914.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___179_20914.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20919;
                         FStar_TypeChecker_Common.element =
                           (uu___179_20914.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_20914.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_20914.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_20914.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_20914.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_20914.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20909 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20921,FStar_Syntax_Syntax.Total uu____20922) ->
                     let uu____20931 =
                       let uu___179_20936 = problem in
                       let uu____20941 =
                         let uu____20942 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20942 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_20936.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___179_20936.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___179_20936.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20941;
                         FStar_TypeChecker_Common.element =
                           (uu___179_20936.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_20936.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_20936.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_20936.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_20936.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_20936.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20931 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20943,FStar_Syntax_Syntax.Comp uu____20944) ->
                     let uu____20945 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____20945
                     then
                       let uu____20946 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____20946 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            &&
                            (FStar_Ident.lid_equals
                               c1_comp.FStar_Syntax_Syntax.effect_name
                               c2_comp.FStar_Syntax_Syntax.effect_name)
                        then solve_eq c1_comp c2_comp
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____20956 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____20956
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____20958 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____20958 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____20961 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____20963 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____20963) in
                                if uu____20961
                                then
                                  let edge =
                                    {
                                      FStar_TypeChecker_Env.msource =
                                        (c12.FStar_Syntax_Syntax.effect_name);
                                      FStar_TypeChecker_Env.mtarget =
                                        (c22.FStar_Syntax_Syntax.effect_name);
                                      FStar_TypeChecker_Env.mlift =
                                        FStar_TypeChecker_Env.identity_mlift
                                    } in
                                  solve_sub c12 edge c22
                                else
                                  (let uu____20966 =
                                     let uu____20967 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____20968 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____20967 uu____20968 in
                                   giveup env uu____20966 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____20974 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21012  ->
              match uu____21012 with
              | (uu____21025,uu____21026,u,uu____21028,uu____21029,uu____21030)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____20974 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21062 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21062 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21080 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21108  ->
                match uu____21108 with
                | (u1,u2) ->
                    let uu____21115 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21116 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21115 uu____21116)) in
      FStar_All.pipe_right uu____21080 (FStar_String.concat ", ") in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
let guard_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.string
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Env.guard_f),
              (g.FStar_TypeChecker_Env.deferred),
              (g.FStar_TypeChecker_Env.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21135,[])) -> "{}"
      | uu____21160 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21177 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21177
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21180 =
              FStar_List.map
                (fun uu____21190  ->
                   match uu____21190 with
                   | (uu____21195,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21180 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21200 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21200 imps
let new_t_problem:
  'Auu____21215 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21215 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21215)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21249 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21249
                then
                  let uu____21250 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21251 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21250
                    (rel_to_string rel) uu____21251
                else "TOP" in
              let p = new_problem env lhs rel rhs elt loc reason in p
let new_t_prob:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.term ->
          (FStar_TypeChecker_Common.prob,FStar_Syntax_Syntax.bv)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t1  ->
      fun rel  ->
        fun t2  ->
          let x =
            let uu____21279 =
              let uu____21282 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____21282 in
            FStar_Syntax_Syntax.new_bv uu____21279 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21291 =
              let uu____21294 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____21294 in
            let uu____21297 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21291 uu____21297 in
          ((FStar_TypeChecker_Common.TProb p), x)
let solve_and_commit:
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob,Prims.string)
         FStar_Pervasives_Native.tuple2 ->
         FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)
        -> FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option
  =
  fun env  ->
    fun probs  ->
      fun err1  ->
        let probs1 =
          let uu____21330 = FStar_Options.eager_inference () in
          if uu____21330
          then
            let uu___180_21331 = probs in
            {
              attempting = (uu___180_21331.attempting);
              wl_deferred = (uu___180_21331.wl_deferred);
              ctr = (uu___180_21331.ctr);
              defer_ok = false;
              smt_ok = (uu___180_21331.smt_ok);
              tcenv = (uu___180_21331.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            (FStar_Syntax_Unionfind.rollback tx;
             (let uu____21343 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21343
              then
                let uu____21344 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21344
              else ());
             err1 (d, s))
let simplify_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____21356 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21356
            then
              let uu____21357 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21357
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f in
            (let uu____21361 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21361
             then
               let uu____21362 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21362
             else ());
            (let f2 =
               let uu____21365 =
                 let uu____21366 = FStar_Syntax_Util.unmeta f1 in
                 uu____21366.FStar_Syntax_Syntax.n in
               match uu____21365 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21370 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___181_21371 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___181_21371.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_21371.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_21371.FStar_TypeChecker_Env.implicits)
             })))
let with_guard:
  FStar_TypeChecker_Env.env ->
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
            let uu____21393 =
              let uu____21394 =
                let uu____21395 =
                  let uu____21396 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21396
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21395;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21394 in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____21393
let with_guard_no_simp:
  'Auu____21427 .
    'Auu____21427 ->
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
            let uu____21447 =
              let uu____21448 =
                let uu____21449 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____21449
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
              {
                FStar_TypeChecker_Env.guard_f = uu____21448;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____21447
let try_teq:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____21491 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21491
           then
             let uu____21492 = FStar_Syntax_Print.term_to_string t1 in
             let uu____21493 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21492
               uu____21493
           else ());
          (let prob =
             let uu____21496 =
               let uu____21501 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____21501 in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____21496 in
           let g =
             let uu____21509 =
               let uu____21512 = singleton' env prob smt_ok in
               solve_and_commit env uu____21512
                 (fun uu____21514  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____21509 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21535 = try_teq true env t1 t2 in
        match uu____21535 with
        | FStar_Pervasives_Native.None  ->
            let uu____21538 =
              let uu____21539 =
                let uu____21544 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____21545 = FStar_TypeChecker_Env.get_range env in
                (uu____21544, uu____21545) in
              FStar_Errors.Error uu____21539 in
            FStar_Exn.raise uu____21538
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21548 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____21548
              then
                let uu____21549 = FStar_Syntax_Print.term_to_string t1 in
                let uu____21550 = FStar_Syntax_Print.term_to_string t2 in
                let uu____21551 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21549
                  uu____21550 uu____21551
              else ());
             g)
let try_subtype':
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        Prims.bool ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun smt_ok  ->
          (let uu____21572 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21572
           then
             let uu____21573 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____21574 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____21573
               uu____21574
           else ());
          (let uu____21576 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____21576 with
           | (prob,x) ->
               let g =
                 let uu____21588 =
                   let uu____21591 = singleton' env prob smt_ok in
                   solve_and_commit env uu____21591
                     (fun uu____21593  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____21588 in
               ((let uu____21603 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____21603
                 then
                   let uu____21604 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____21605 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____21606 =
                     let uu____21607 = FStar_Util.must g in
                     guard_to_string env uu____21607 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____21604 uu____21605 uu____21606
                 else ());
                abstract_guard x g))
let try_subtype:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  = fun env  -> fun t1  -> fun t2  -> try_subtype' env t1 t2 true
let subtype_fail:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____21639 = FStar_TypeChecker_Env.get_range env in
          let uu____21640 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____21639 uu____21640
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____21656 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____21656
         then
           let uu____21657 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____21658 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____21657
             uu____21658
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____21663 =
             let uu____21668 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____21668 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____21663 in
         let uu____21673 =
           let uu____21676 = singleton env prob in
           solve_and_commit env uu____21676
             (fun uu____21678  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____21673)
let solve_universe_inequalities':
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                                 FStar_Syntax_Syntax.universe)
                                                 FStar_Pervasives_Native.tuple2
                                                 Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____21710  ->
        match uu____21710 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____21749 =
                 let uu____21750 =
                   let uu____21755 =
                     let uu____21756 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____21757 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____21756 uu____21757 in
                   let uu____21758 = FStar_TypeChecker_Env.get_range env in
                   (uu____21755, uu____21758) in
                 FStar_Errors.Error uu____21750 in
               FStar_Exn.raise uu____21749) in
            let equiv1 v1 v' =
              let uu____21766 =
                let uu____21771 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____21772 = FStar_Syntax_Subst.compress_univ v' in
                (uu____21771, uu____21772) in
              match uu____21766 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____21791 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____21821 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____21821 with
                      | FStar_Syntax_Syntax.U_unif uu____21828 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____21857  ->
                                    match uu____21857 with
                                    | (u,v') ->
                                        let uu____21866 = equiv1 v1 v' in
                                        if uu____21866
                                        then
                                          let uu____21869 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____21869 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____21885 -> [])) in
            let uu____21890 =
              let wl =
                let uu___182_21894 = empty_worklist env in
                {
                  attempting = (uu___182_21894.attempting);
                  wl_deferred = (uu___182_21894.wl_deferred);
                  ctr = (uu___182_21894.ctr);
                  defer_ok = false;
                  smt_ok = (uu___182_21894.smt_ok);
                  tcenv = (uu___182_21894.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____21912  ->
                      match uu____21912 with
                      | (lb,v1) ->
                          let uu____21919 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____21919 with
                           | USolved wl1 -> ()
                           | uu____21921 -> fail lb v1))) in
            let rec check_ineq uu____21929 =
              match uu____21929 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____21938) -> true
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
                      uu____21961,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____21963,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____21974) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____21981,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____21989 -> false) in
            let uu____21994 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22009  ->
                      match uu____22009 with
                      | (u,v1) ->
                          let uu____22016 = check_ineq (u, v1) in
                          if uu____22016
                          then true
                          else
                            ((let uu____22019 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____22019
                              then
                                let uu____22020 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____22021 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____22020
                                  uu____22021
                              else ());
                             false))) in
            if uu____21994
            then ()
            else
              ((let uu____22025 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____22025
                then
                  ((let uu____22027 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22027);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22037 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22037))
                else ());
               (let uu____22047 =
                  let uu____22048 =
                    let uu____22053 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____22053) in
                  FStar_Errors.Error uu____22048 in
                FStar_Exn.raise uu____22047))
let solve_universe_inequalities:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                               FStar_Syntax_Syntax.universe)
                                               FStar_Pervasives_Native.tuple2
                                               Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun env  ->
    fun ineqs  ->
      let tx = FStar_Syntax_Unionfind.new_transaction () in
      solve_universe_inequalities' tx env ineqs;
      FStar_Syntax_Unionfind.commit tx
let rec solve_deferred_constraints:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let fail uu____22105 =
        match uu____22105 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Exn.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22119 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22119
       then
         let uu____22120 = wl_to_string wl in
         let uu____22121 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22120 uu____22121
       else ());
      (let g1 =
         let uu____22136 = solve_and_commit env wl fail in
         match uu____22136 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___183_22149 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___183_22149.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___183_22149.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___183_22149.FStar_TypeChecker_Env.implicits)
             }
         | uu____22154 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___184_22158 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___184_22158.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___184_22158.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___184_22158.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22181 = FStar_ST.op_Bang last_proof_ns in
    match uu____22181 with
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
let discharge_guard':
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let g1 = solve_deferred_constraints env g in
          let ret_g =
            let uu___185_22272 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___185_22272.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___185_22272.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___185_22272.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22273 =
            let uu____22274 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22274 in
          if uu____22273
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____22282 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____22282
                   then
                     let uu____22283 = FStar_TypeChecker_Env.get_range env in
                     let uu____22284 =
                       let uu____22285 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22285 in
                     FStar_Errors.diag uu____22283 uu____22284
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   let uu____22288 = check_trivial vc1 in
                   match uu____22288 with
                   | FStar_TypeChecker_Common.Trivial  ->
                       FStar_Pervasives_Native.Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then
                         ((let uu____22295 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____22295
                           then
                             let uu____22296 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____22297 =
                               let uu____22298 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1
                                 "Cannot solve without SMT : %s\n"
                                 uu____22298 in
                             FStar_Errors.diag uu____22296 uu____22297
                           else ());
                          FStar_Pervasives_Native.None)
                       else
                         ((let uu____22303 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____22303
                           then
                             let uu____22304 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____22305 =
                               let uu____22306 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____22306 in
                             FStar_Errors.diag uu____22304 uu____22305
                           else ());
                          (let vcs =
                             let uu____22317 = FStar_Options.use_tactics () in
                             if uu____22317
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else
                               (let uu____22327 =
                                  let uu____22334 = FStar_Options.peek () in
                                  (env, vc2, uu____22334) in
                                [uu____22327]) in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____22368  ->
                                   match uu____22368 with
                                   | (env1,goal,opts) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify;
                                           FStar_TypeChecker_Normalize.Primops]
                                           env1 goal in
                                       let uu____22379 = check_trivial goal1 in
                                       (match uu____22379 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____22381 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____22381
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            (FStar_Options.push ();
                                             FStar_Options.set opts;
                                             maybe_update_proof_ns env1;
                                             (let uu____22388 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____22388
                                              then
                                                let uu____22389 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____22390 =
                                                  let uu____22391 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____22392 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____22391 uu____22392 in
                                                FStar_Errors.diag uu____22389
                                                  uu____22390
                                              else ());
                                             (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                               use_env_range_msg env1 goal2;
                                             FStar_Options.pop ())))));
                          FStar_Pervasives_Native.Some ret_g))))
let discharge_guard_no_smt:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22404 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22404 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22410 =
            let uu____22411 =
              let uu____22416 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____22416) in
            FStar_Errors.Error uu____22411 in
          FStar_Exn.raise uu____22410
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22425 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____22425 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits':
  Prims.bool ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun forcelax  ->
    fun g  ->
      let unresolved u =
        let uu____22443 = FStar_Syntax_Unionfind.find u in
        match uu____22443 with
        | FStar_Pervasives_Native.None  -> true
        | uu____22446 -> false in
      let rec until_fixpoint acc implicits =
        let uu____22464 = acc in
        match uu____22464 with
        | (out,changed) ->
            (match implicits with
             | [] ->
                 if Prims.op_Negation changed
                 then out
                 else until_fixpoint ([], false) out
             | hd1::tl1 ->
                 let uu____22550 = hd1 in
                 (match uu____22550 with
                  | (uu____22563,env,u,tm,k,r) ->
                      let uu____22569 = unresolved u in
                      if uu____22569
                      then until_fixpoint ((hd1 :: out), changed) tl1
                      else
                        (let env1 =
                           FStar_TypeChecker_Env.set_expected_typ env k in
                         let tm1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta] env1 tm in
                         (let uu____22600 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "RelCheck") in
                          if uu____22600
                          then
                            let uu____22601 =
                              FStar_Syntax_Print.uvar_to_string u in
                            let uu____22602 =
                              FStar_Syntax_Print.term_to_string tm1 in
                            let uu____22603 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print3
                              "Checking uvar %s resolved to %s at type %s\n"
                              uu____22601 uu____22602 uu____22603
                          else ());
                         (let env2 =
                            if forcelax
                            then
                              let uu___186_22606 = env1 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___186_22606.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___186_22606.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___186_22606.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___186_22606.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___186_22606.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___186_22606.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___186_22606.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___186_22606.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___186_22606.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___186_22606.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___186_22606.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___186_22606.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___186_22606.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___186_22606.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___186_22606.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___186_22606.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___186_22606.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___186_22606.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___186_22606.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___186_22606.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___186_22606.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___186_22606.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___186_22606.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___186_22606.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___186_22606.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___186_22606.FStar_TypeChecker_Env.is_native_tactic)
                              }
                            else env1 in
                          let uu____22608 =
                            env2.FStar_TypeChecker_Env.type_of
                              (let uu___187_22616 = env2 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___187_22616.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___187_22616.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___187_22616.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___187_22616.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___187_22616.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___187_22616.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___187_22616.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___187_22616.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___187_22616.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___187_22616.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___187_22616.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___187_22616.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___187_22616.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___187_22616.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___187_22616.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___187_22616.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___187_22616.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___187_22616.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___187_22616.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___187_22616.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___187_22616.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___187_22616.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___187_22616.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___187_22616.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___187_22616.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___187_22616.FStar_TypeChecker_Env.is_native_tactic)
                               }) tm1 in
                          match uu____22608 with
                          | (uu____22617,uu____22618,g1) ->
                              let g2 =
                                if env2.FStar_TypeChecker_Env.is_pattern
                                then
                                  let uu___188_22621 = g1 in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      FStar_TypeChecker_Common.Trivial;
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___188_22621.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___188_22621.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits =
                                      (uu___188_22621.FStar_TypeChecker_Env.implicits)
                                  }
                                else g1 in
                              let g' =
                                let uu____22624 =
                                  discharge_guard'
                                    (FStar_Pervasives_Native.Some
                                       (fun uu____22630  ->
                                          FStar_Syntax_Print.term_to_string
                                            tm1)) env2 g2 true in
                                match uu____22624 with
                                | FStar_Pervasives_Native.Some g3 -> g3
                                | FStar_Pervasives_Native.None  ->
                                    failwith
                                      "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                              until_fixpoint
                                ((FStar_List.append
                                    g'.FStar_TypeChecker_Env.implicits out),
                                  true) tl1)))) in
      let uu___189_22658 = g in
      let uu____22659 =
        until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___189_22658.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___189_22658.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs =
          (uu___189_22658.FStar_TypeChecker_Env.univ_ineqs);
        FStar_TypeChecker_Env.implicits = uu____22659
      }
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  -> resolve_implicits' false g
let resolve_implicits_lax:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  -> resolve_implicits' true g
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____22717 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____22717 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____22730 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____22730
      | (reason,uu____22732,uu____22733,e,t,r)::uu____22737 ->
          let uu____22764 =
            let uu____22765 =
              let uu____22770 =
                let uu____22771 = FStar_Syntax_Print.term_to_string t in
                let uu____22772 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____22771 uu____22772 in
              (uu____22770, r) in
            FStar_Errors.Error uu____22765 in
          FStar_Exn.raise uu____22764
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___190_22781 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___190_22781.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___190_22781.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___190_22781.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22810 = try_teq false env t1 t2 in
        match uu____22810 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____22814 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____22814 with
             | FStar_Pervasives_Native.Some uu____22819 -> true
             | FStar_Pervasives_Native.None  -> false)