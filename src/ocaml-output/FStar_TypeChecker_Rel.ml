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
  fun uu____1430  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem:
  'Auu____1455 'Auu____1456 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1456 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1456 ->
              'Auu____1455 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1456,'Auu____1455)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1493 = next_pid () in
                let uu____1494 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1493;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1494;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let new_problem:
  'Auu____1517 'Auu____1518 .
    FStar_TypeChecker_Env.env ->
      'Auu____1518 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1518 ->
            'Auu____1517 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1518,'Auu____1517)
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
                let uu____1556 = next_pid () in
                let uu____1557 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1556;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1557;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let problem_using_guard:
  'Auu____1578 'Auu____1579 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1579 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1579 ->
            'Auu____1578 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1579,'Auu____1578) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____1612 = next_pid () in
              {
                FStar_TypeChecker_Common.pid = uu____1612;
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
  'Auu____1623 .
    worklist ->
      ('Auu____1623,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
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
        let uu____1676 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1676
        then
          let uu____1677 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1678 = prob_to_string env d in
          let uu____1679 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1677 uu____1678 uu____1679 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1685 -> failwith "impossible" in
           let uu____1686 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1700 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1701 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1700, uu____1701)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1707 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1708 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1707, uu____1708) in
           match uu____1686 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___120_1725  ->
            match uu___120_1725 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1737 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1739),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___121_1761  ->
           match uu___121_1761 with
           | UNIV uu____1764 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1770),t) ->
               let uu____1776 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1776
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
        (fun uu___122_1798  ->
           match uu___122_1798 with
           | UNIV (u',t) ->
               let uu____1803 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1803
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1807 -> FStar_Pervasives_Native.None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1816 =
        let uu____1817 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1817 in
      FStar_Syntax_Subst.compress uu____1816
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1826 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1826
let norm_arg:
  'Auu____1833 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____1833) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1833)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____1854 = sn env (FStar_Pervasives_Native.fst t) in
      (uu____1854, (FStar_Pervasives_Native.snd t))
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
           (fun uu____1887  ->
              match uu____1887 with
              | (x,imp) ->
                  let uu____1898 =
                    let uu___145_1899 = x in
                    let uu____1900 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___145_1899.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___145_1899.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1900
                    } in
                  (uu____1898, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1917 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1917
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1921 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1921
        | uu____1924 -> u2 in
      let uu____1925 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1925
let normalize_refinement:
  'Auu____1936 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____1936 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun steps  ->
    fun env  ->
      fun wl  ->
        fun t0  ->
          FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement:
  'Auu____1961 .
    FStar_TypeChecker_Env.env ->
      'Auu____1961 ->
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
        let rec aux norm t11 =
          match t11.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____2066 =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 match uu____2066 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2083;
                     FStar_Syntax_Syntax.vars = uu____2084;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2110 =
                       let uu____2111 = FStar_Syntax_Print.term_to_string tt in
                       let uu____2112 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2111 uu____2112 in
                     failwith uu____2110)
          | FStar_Syntax_Syntax.Tm_uinst uu____2127 ->
              if norm
              then (t11, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 let uu____2166 =
                   let uu____2167 = FStar_Syntax_Subst.compress t1' in
                   uu____2167.FStar_Syntax_Syntax.n in
                 match uu____2166 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2184 -> aux true t1'
                 | uu____2191 -> (t11, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2208 ->
              if norm
              then (t11, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 let uu____2241 =
                   let uu____2242 = FStar_Syntax_Subst.compress t1' in
                   uu____2242.FStar_Syntax_Syntax.n in
                 match uu____2241 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2259 -> aux true t1'
                 | uu____2266 -> (t11, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2283 ->
              if norm
              then (t11, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 let uu____2330 =
                   let uu____2331 = FStar_Syntax_Subst.compress t1' in
                   uu____2331.FStar_Syntax_Syntax.n in
                 match uu____2330 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2348 -> aux true t1'
                 | uu____2355 -> (t11, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2372 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2389 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2406 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2423 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2440 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2469 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2502 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2535 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2564 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2603 ->
              let uu____2610 =
                let uu____2611 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2612 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2611 uu____2612 in
              failwith uu____2610
          | FStar_Syntax_Syntax.Tm_ascribed uu____2627 ->
              let uu____2654 =
                let uu____2655 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2656 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2655 uu____2656 in
              failwith uu____2654
          | FStar_Syntax_Syntax.Tm_delayed uu____2671 ->
              let uu____2696 =
                let uu____2697 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2698 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2697 uu____2698 in
              failwith uu____2696
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2713 =
                let uu____2714 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2715 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2714 uu____2715 in
              failwith uu____2713 in
        let uu____2730 = whnf env t1 in aux false uu____2730
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun t  ->
      let uu____2741 =
        let uu____2756 = empty_worklist env in
        base_and_refinement env uu____2756 t in
      FStar_All.pipe_right uu____2741 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2791 = FStar_Syntax_Syntax.null_bv t in
    (uu____2791, FStar_Syntax_Util.t_true)
let as_refinement:
  'Auu____2800 .
    FStar_TypeChecker_Env.env ->
      'Auu____2800 ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun t  ->
        let uu____2817 = base_and_refinement env wl t in
        match uu____2817 with
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
  fun uu____2897  ->
    match uu____2897 with
    | (t_base,refopt) ->
        let uu____2924 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
        (match uu____2924 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___123_2954  ->
      match uu___123_2954 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2960 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2961 =
            let uu____2962 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____2962 in
          let uu____2963 =
            let uu____2964 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____2964 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2960 uu____2961
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2963
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2970 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2971 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____2972 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2970 uu____2971
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2972
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2977 =
      let uu____2980 =
        let uu____2983 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3006  ->
                  match uu____3006 with | (uu____3013,uu____3014,x) -> x)) in
        FStar_List.append wl.attempting uu____2983 in
      FStar_List.map (wl_prob_to_string wl) uu____2980 in
    FStar_All.pipe_right uu____2977 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3042 =
          let uu____3061 =
            let uu____3062 = FStar_Syntax_Subst.compress k in
            uu____3062.FStar_Syntax_Syntax.n in
          match uu____3061 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3127 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____3127)
              else
                (let uu____3153 = FStar_Syntax_Util.abs_formals t in
                 match uu____3153 with
                 | (ys',t1,uu____3182) ->
                     let uu____3187 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3187))
          | uu____3228 ->
              let uu____3229 =
                let uu____3240 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3240) in
              ((ys, t), uu____3229) in
        match uu____3042 with
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
                 let uu____3319 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3319 c in
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
            let uu____3352 = p_guard prob in
            match uu____3352 with
            | (uu____3357,uv) ->
                ((let uu____3360 =
                    let uu____3361 = FStar_Syntax_Subst.compress uv in
                    uu____3361.FStar_Syntax_Syntax.n in
                  match uu____3360 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3393 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3393
                        then
                          let uu____3394 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3395 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3396 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3394
                            uu____3395 uu____3396
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3398 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___146_3401 = wl in
                  {
                    attempting = (uu___146_3401.attempting);
                    wl_deferred = (uu___146_3401.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___146_3401.defer_ok);
                    smt_ok = (uu___146_3401.smt_ok);
                    tcenv = (uu___146_3401.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3419 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3419
         then
           let uu____3420 = FStar_Util.string_of_int pid in
           let uu____3421 =
             let uu____3422 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3422 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3420 uu____3421
         else ());
        commit sol;
        (let uu___147_3429 = wl in
         {
           attempting = (uu___147_3429.attempting);
           wl_deferred = (uu___147_3429.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___147_3429.defer_ok);
           smt_ok = (uu___147_3429.smt_ok);
           tcenv = (uu___147_3429.tcenv)
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
            | (uu____3471,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3483 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3483 in
          (let uu____3489 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3489
           then
             let uu____3490 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3491 =
               let uu____3492 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3492 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3490 uu____3491
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
        let uu____3527 =
          let uu____3534 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3534 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3527
          (FStar_Util.for_some
             (fun uu____3570  ->
                match uu____3570 with
                | (uv,uu____3576) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check:
  'Auu____3589 'Auu____3590 .
    'Auu____3590 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3589)
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
            let uu____3622 = occurs wl uk t in Prims.op_Negation uu____3622 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3629 =
                 let uu____3630 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3631 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3630 uu____3631 in
               FStar_Pervasives_Native.Some uu____3629) in
          (occurs_ok, msg)
let occurs_and_freevars_check:
  'Auu____3648 'Auu____3649 .
    'Auu____3649 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3648)
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
            let uu____3703 = occurs_check env wl uk t in
            match uu____3703 with
            | (occurs_ok,msg) ->
                let uu____3734 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3734, (msg, fvs, fvs_t))
let intersect_vars:
  'Auu____3761 'Auu____3762 .
    (FStar_Syntax_Syntax.bv,'Auu____3762) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3761) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3761) FStar_Pervasives_Native.tuple2
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
      let uu____3846 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3900  ->
                fun uu____3901  ->
                  match (uu____3900, uu____3901) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3982 =
                        let uu____3983 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____3983 in
                      if uu____3982
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____4008 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____4008
                         then
                           let uu____4021 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____4021)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3846 with | (isect,uu____4062) -> FStar_List.rev isect
let binders_eq:
  'Auu____4091 'Auu____4092 .
    (FStar_Syntax_Syntax.bv,'Auu____4092) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4091) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4147  ->
              fun uu____4148  ->
                match (uu____4147, uu____4148) with
                | ((a,uu____4166),(b,uu____4168)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt:
  'Auu____4187 'Auu____4188 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____4188) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____4187)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____4187)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4239 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4253  ->
                      match uu____4253 with
                      | (b,uu____4259) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____4239
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4275 -> FStar_Pervasives_Native.None
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
            let uu____4350 = pat_var_opt env seen hd1 in
            (match uu____4350 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4364 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4364
                   then
                     let uu____4365 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4365
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4384 =
      let uu____4385 = FStar_Syntax_Subst.compress t in
      uu____4385.FStar_Syntax_Syntax.n in
    match uu____4384 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4388 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4405;
           FStar_Syntax_Syntax.pos = uu____4406;
           FStar_Syntax_Syntax.vars = uu____4407;_},uu____4408)
        -> true
    | uu____4445 -> false
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
           FStar_Syntax_Syntax.pos = uu____4570;
           FStar_Syntax_Syntax.vars = uu____4571;_},args)
        -> (t, uv, k, args)
    | uu____4639 -> failwith "Not a flex-uvar"
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
      let uu____4718 = destruct_flex_t t in
      match uu____4718 with
      | (t1,uv,k,args) ->
          let uu____4833 = pat_vars env [] args in
          (match uu____4833 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4931 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5013 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5050 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5055 -> false
let head_match: match_result -> match_result =
  fun uu___124_5059  ->
    match uu___124_5059 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5074 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5085 ->
          let uu____5086 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____5086 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5097 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5118 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5127 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5154 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5155 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5156 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5173 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5186 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5210) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5216,uu____5217) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5259) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5280;
             FStar_Syntax_Syntax.index = uu____5281;
             FStar_Syntax_Syntax.sort = t2;_},uu____5283)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5290 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5291 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5292 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5305 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5323 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5323
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
            let uu____5347 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5347
            then FullMatch
            else
              (let uu____5349 =
                 let uu____5358 =
                   let uu____5361 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5361 in
                 let uu____5362 =
                   let uu____5365 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5365 in
                 (uu____5358, uu____5362) in
               MisMatch uu____5349)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5371),FStar_Syntax_Syntax.Tm_uinst (g,uu____5373)) ->
            let uu____5382 = head_matches env f g in
            FStar_All.pipe_right uu____5382 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5391),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5393)) ->
            let uu____5442 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5442
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5449),FStar_Syntax_Syntax.Tm_refine (y,uu____5451)) ->
            let uu____5460 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5460 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5462),uu____5463) ->
            let uu____5468 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5468 head_match
        | (uu____5469,FStar_Syntax_Syntax.Tm_refine (x,uu____5471)) ->
            let uu____5476 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5476 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5477,FStar_Syntax_Syntax.Tm_type
           uu____5478) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5479,FStar_Syntax_Syntax.Tm_arrow uu____5480) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5506),FStar_Syntax_Syntax.Tm_app (head',uu____5508))
            ->
            let uu____5549 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5549 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5551),uu____5552) ->
            let uu____5573 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5573 head_match
        | (uu____5574,FStar_Syntax_Syntax.Tm_app (head1,uu____5576)) ->
            let uu____5597 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5597 head_match
        | uu____5598 ->
            let uu____5603 =
              let uu____5612 = delta_depth_of_term env t11 in
              let uu____5615 = delta_depth_of_term env t21 in
              (uu____5612, uu____5615) in
            MisMatch uu____5603
let head_matches_delta:
  'Auu____5632 .
    FStar_TypeChecker_Env.env ->
      'Auu____5632 ->
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
            let uu____5665 = FStar_Syntax_Util.head_and_args t in
            match uu____5665 with
            | (head1,uu____5683) ->
                let uu____5704 =
                  let uu____5705 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5705.FStar_Syntax_Syntax.n in
                (match uu____5704 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5711 =
                       let uu____5712 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5712 FStar_Option.isSome in
                     if uu____5711
                     then
                       let uu____5731 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5731
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____5735 -> FStar_Pervasives_Native.None) in
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5838)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5856 =
                     let uu____5865 = maybe_inline t11 in
                     let uu____5868 = maybe_inline t21 in
                     (uu____5865, uu____5868) in
                   match uu____5856 with
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
                (uu____5905,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5923 =
                     let uu____5932 = maybe_inline t11 in
                     let uu____5935 = maybe_inline t21 in
                     (uu____5932, uu____5935) in
                   match uu____5923 with
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
                let uu____5978 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____5978 with
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
                let uu____6001 =
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
                (match uu____6001 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6025 -> fail r
            | uu____6034 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____6068 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____6106 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6125 = FStar_Syntax_Util.type_u () in
      match uu____6125 with
      | (t,uu____6131) ->
          let uu____6132 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____6132
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6145 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____6145 FStar_Pervasives_Native.fst
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
        let uu____6211 = head_matches env t1 t' in
        match uu____6211 with
        | MisMatch uu____6212 -> false
        | uu____6221 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6317,imp),T (t2,uu____6320)) -> (t2, imp)
                     | uu____6339 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6406  ->
                    match uu____6406 with
                    | (t2,uu____6420) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6463 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6463 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6538))::tcs2) ->
                       aux
                         (((let uu___148_6573 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_6573.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_6573.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6591 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___125_6644 =
                 match uu___125_6644 with
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
               let uu____6761 = decompose1 [] bs1 in
               (rebuild, matches, uu____6761))
      | uu____6810 ->
          let rebuild uu___126_6816 =
            match uu___126_6816 with
            | [] -> t1
            | uu____6819 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___127_6851  ->
    match uu___127_6851 with
    | T (t,uu____6853) -> t
    | uu____6862 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___128_6866  ->
    match uu___128_6866 with
    | T (t,uu____6868) -> FStar_Syntax_Syntax.as_arg t
    | uu____6877 -> failwith "Impossible"
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
              | (uu____6988,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____7013 = new_uvar r scope1 k in
                  (match uu____7013 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7031 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____7048 =
                         let uu____7049 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____7049 in
                       ((T (gi_xs, mk_kind)), uu____7048))
              | (uu____7062,uu____7063,C uu____7064) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7211 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7228;
                         FStar_Syntax_Syntax.vars = uu____7229;_})
                        ->
                        let uu____7252 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7252 with
                         | (T (gi_xs,uu____7276),prob) ->
                             let uu____7286 =
                               let uu____7287 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____7287 in
                             (uu____7286, [prob])
                         | uu____7290 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7305;
                         FStar_Syntax_Syntax.vars = uu____7306;_})
                        ->
                        let uu____7329 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7329 with
                         | (T (gi_xs,uu____7353),prob) ->
                             let uu____7363 =
                               let uu____7364 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7364 in
                             (uu____7363, [prob])
                         | uu____7367 -> failwith "impossible")
                    | (uu____7378,uu____7379,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7381;
                         FStar_Syntax_Syntax.vars = uu____7382;_})
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
                        let uu____7513 =
                          let uu____7522 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7522 FStar_List.unzip in
                        (match uu____7513 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7576 =
                                 let uu____7577 =
                                   let uu____7580 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7580 un_T in
                                 let uu____7581 =
                                   let uu____7590 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7590
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7577;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7581;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7576 in
                             ((C gi_xs), sub_probs))
                    | uu____7599 ->
                        let uu____7612 = sub_prob scope1 args q in
                        (match uu____7612 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____7211 with
                   | (tc,probs) ->
                       let uu____7643 =
                         match q with
                         | (FStar_Pervasives_Native.Some
                            b,uu____7693,uu____7694) ->
                             let uu____7709 =
                               let uu____7716 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____7716 :: args in
                             ((FStar_Pervasives_Native.Some b), (b ::
                               scope1), uu____7709)
                         | uu____7751 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7643 with
                        | (bopt,scope2,args1) ->
                            let uu____7831 = aux scope2 args1 qs2 in
                            (match uu____7831 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7868 =
                                         let uu____7871 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____7871 in
                                       FStar_Syntax_Util.mk_conj_l uu____7868
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____7894 =
                                         let uu____7897 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____7898 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____7897 :: uu____7898 in
                                       FStar_Syntax_Util.mk_conj_l uu____7894 in
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
  'Auu____7969 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____7969)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____7969)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___149_7990 = p in
      let uu____7995 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____7996 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___149_7990.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7995;
        FStar_TypeChecker_Common.relation =
          (uu___149_7990.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7996;
        FStar_TypeChecker_Common.element =
          (uu___149_7990.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___149_7990.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___149_7990.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___149_7990.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___149_7990.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___149_7990.FStar_TypeChecker_Common.rank)
      }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8010 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____8010
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____8019 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8041 = compress_prob wl pr in
        FStar_All.pipe_right uu____8041 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8051 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8051 with
           | (lh,uu____8071) ->
               let uu____8092 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8092 with
                | (rh,uu____8112) ->
                    let uu____8133 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8150,FStar_Syntax_Syntax.Tm_uvar uu____8151)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8188,uu____8189)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8210,FStar_Syntax_Syntax.Tm_uvar uu____8211)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8232,uu____8233)
                          ->
                          let uu____8250 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____8250 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8313 ->
                                    let rank =
                                      let uu____8323 = is_top_level_prob prob in
                                      if uu____8323
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8325 =
                                      let uu___150_8330 = tp in
                                      let uu____8335 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___150_8330.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___150_8330.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___150_8330.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8335;
                                        FStar_TypeChecker_Common.element =
                                          (uu___150_8330.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___150_8330.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___150_8330.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___150_8330.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___150_8330.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___150_8330.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8325)))
                      | (uu____8350,FStar_Syntax_Syntax.Tm_uvar uu____8351)
                          ->
                          let uu____8368 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8368 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8431 ->
                                    let uu____8440 =
                                      let uu___151_8447 = tp in
                                      let uu____8452 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___151_8447.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8452;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___151_8447.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___151_8447.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___151_8447.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___151_8447.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___151_8447.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___151_8447.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___151_8447.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___151_8447.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8440)))
                      | (uu____8473,uu____8474) -> (rigid_rigid, tp) in
                    (match uu____8133 with
                     | (rank,tp1) ->
                         let uu____8493 =
                           FStar_All.pipe_right
                             (let uu___152_8499 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___152_8499.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___152_8499.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___152_8499.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___152_8499.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___152_8499.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___152_8499.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___152_8499.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___152_8499.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___152_8499.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50) in
                         (rank, uu____8493))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8509 =
            FStar_All.pipe_right
              (let uu___153_8515 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___153_8515.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___153_8515.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___153_8515.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___153_8515.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___153_8515.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___153_8515.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___153_8515.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___153_8515.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___153_8515.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51) in
          (rigid_rigid, uu____8509)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____8571 probs =
      match uu____8571 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8624 = rank wl hd1 in
               (match uu____8624 with
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
    match projectee with | UDeferred _0 -> true | uu____8734 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8748 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8762 -> false
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
                        let uu____8807 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8807 with
                        | (k,uu____8813) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8823 -> false)))
            | uu____8824 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____8875 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____8875 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8878 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____8888 =
                     let uu____8889 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____8890 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8889
                       uu____8890 in
                   UFailed uu____8888)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8910 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8910 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8932 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8932 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____8935 ->
                let uu____8940 =
                  let uu____8941 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____8942 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8941
                    uu____8942 msg in
                UFailed uu____8940 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8943,uu____8944) ->
              let uu____8945 =
                let uu____8946 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8947 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8946 uu____8947 in
              failwith uu____8945
          | (FStar_Syntax_Syntax.U_unknown ,uu____8948) ->
              let uu____8949 =
                let uu____8950 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8951 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8950 uu____8951 in
              failwith uu____8949
          | (uu____8952,FStar_Syntax_Syntax.U_bvar uu____8953) ->
              let uu____8954 =
                let uu____8955 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8956 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8955 uu____8956 in
              failwith uu____8954
          | (uu____8957,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8958 =
                let uu____8959 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8960 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8959 uu____8960 in
              failwith uu____8958
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8984 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____8984
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____9006 = occurs_univ v1 u3 in
              if uu____9006
              then
                let uu____9007 =
                  let uu____9008 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9009 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9008 uu____9009 in
                try_umax_components u11 u21 uu____9007
              else
                (let uu____9011 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9011)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9031 = occurs_univ v1 u3 in
              if uu____9031
              then
                let uu____9032 =
                  let uu____9033 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9034 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9033 uu____9034 in
                try_umax_components u11 u21 uu____9032
              else
                (let uu____9036 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9036)
          | (FStar_Syntax_Syntax.U_max uu____9045,uu____9046) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9052 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9052
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9054,FStar_Syntax_Syntax.U_max uu____9055) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9061 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9061
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9063,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9064,FStar_Syntax_Syntax.U_name
             uu____9065) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9066) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9067) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9068,FStar_Syntax_Syntax.U_succ
             uu____9069) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9070,FStar_Syntax_Syntax.U_zero
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
      let uu____9164 = bc1 in
      match uu____9164 with
      | (bs1,mk_cod1) ->
          let uu____9205 = bc2 in
          (match uu____9205 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____9275 = FStar_Util.first_N n1 bs in
                 match uu____9275 with
                 | (bs3,rest) ->
                     let uu____9300 = mk_cod rest in (bs3, uu____9300) in
               let l1 = FStar_List.length bs1 in
               let l2 = FStar_List.length bs2 in
               if l1 = l2
               then
                 let uu____9329 =
                   let uu____9336 = mk_cod1 [] in (bs1, uu____9336) in
                 let uu____9339 =
                   let uu____9346 = mk_cod2 [] in (bs2, uu____9346) in
                 (uu____9329, uu____9339)
               else
                 if l1 > l2
                 then
                   (let uu____9388 = curry l2 bs1 mk_cod1 in
                    let uu____9401 =
                      let uu____9408 = mk_cod2 [] in (bs2, uu____9408) in
                    (uu____9388, uu____9401))
                 else
                   (let uu____9424 =
                      let uu____9431 = mk_cod1 [] in (bs1, uu____9431) in
                    let uu____9434 = curry l1 bs2 mk_cod2 in
                    (uu____9424, uu____9434)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____9555 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9555
       then
         let uu____9556 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9556
       else ());
      (let uu____9558 = next_prob probs in
       match uu____9558 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___154_9579 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___154_9579.wl_deferred);
               ctr = (uu___154_9579.ctr);
               defer_ok = (uu___154_9579.defer_ok);
               smt_ok = (uu___154_9579.smt_ok);
               tcenv = (uu___154_9579.tcenv)
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
                  let uu____9590 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9590 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9595 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9595 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9600,uu____9601) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9618 ->
                let uu____9627 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9686  ->
                          match uu____9686 with
                          | (c,uu____9694,uu____9695) -> c < probs.ctr)) in
                (match uu____9627 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9736 =
                            FStar_List.map
                              (fun uu____9751  ->
                                 match uu____9751 with
                                 | (uu____9762,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____9736
                      | uu____9765 ->
                          let uu____9774 =
                            let uu___155_9775 = probs in
                            let uu____9776 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9797  ->
                                      match uu____9797 with
                                      | (uu____9804,uu____9805,y) -> y)) in
                            {
                              attempting = uu____9776;
                              wl_deferred = rest;
                              ctr = (uu___155_9775.ctr);
                              defer_ok = (uu___155_9775.defer_ok);
                              smt_ok = (uu___155_9775.smt_ok);
                              tcenv = (uu___155_9775.tcenv)
                            } in
                          solve env uu____9774))))
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
            let uu____9812 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____9812 with
            | USolved wl1 ->
                let uu____9814 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____9814
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
                  let uu____9860 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____9860 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9863 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9875;
                  FStar_Syntax_Syntax.vars = uu____9876;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9879;
                  FStar_Syntax_Syntax.vars = uu____9880;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9894,uu____9895) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9902,FStar_Syntax_Syntax.Tm_uinst uu____9903) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9910 -> USolved wl
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
            ((let uu____9920 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____9920
              then
                let uu____9921 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9921 msg
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
        (let uu____9930 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____9930
         then
           let uu____9931 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____9931
         else ());
        (let uu____9933 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____9933 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____9995 = head_matches_delta env () t1 t2 in
               match uu____9995 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10036 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10085 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10100 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____10101 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____10100, uu____10101)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10106 =
                                FStar_Syntax_Subst.compress t1 in
                              let uu____10107 =
                                FStar_Syntax_Subst.compress t2 in
                              (uu____10106, uu____10107) in
                        (match uu____10085 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10133 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____10133 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10164 =
                                    let uu____10173 =
                                      let uu____10176 =
                                        let uu____10179 =
                                          let uu____10180 =
                                            let uu____10187 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____10187) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10180 in
                                        FStar_Syntax_Syntax.mk uu____10179 in
                                      uu____10176
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____10195 =
                                      let uu____10198 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____10198] in
                                    (uu____10173, uu____10195) in
                                  FStar_Pervasives_Native.Some uu____10164
                              | (uu____10211,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10213)) ->
                                  let uu____10218 =
                                    let uu____10225 =
                                      let uu____10228 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____10228] in
                                    (t11, uu____10225) in
                                  FStar_Pervasives_Native.Some uu____10218
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10238),uu____10239) ->
                                  let uu____10244 =
                                    let uu____10251 =
                                      let uu____10254 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____10254] in
                                    (t21, uu____10251) in
                                  FStar_Pervasives_Native.Some uu____10244
                              | uu____10263 ->
                                  let uu____10268 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____10268 with
                                   | (head1,uu____10292) ->
                                       let uu____10313 =
                                         let uu____10314 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____10314.FStar_Syntax_Syntax.n in
                                       (match uu____10313 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10325;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10327;_}
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
                                        | uu____10334 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10347) ->
                  let uu____10372 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___129_10398  ->
                            match uu___129_10398 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10405 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10405 with
                                      | (u',uu____10421) ->
                                          let uu____10442 =
                                            let uu____10443 = whnf env u' in
                                            uu____10443.FStar_Syntax_Syntax.n in
                                          (match uu____10442 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10447) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10472 -> false))
                                 | uu____10473 -> false)
                            | uu____10476 -> false)) in
                  (match uu____10372 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10510 tps =
                         match uu____10510 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10558 =
                                    let uu____10567 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10567 in
                                  (match uu____10558 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10602 -> FStar_Pervasives_Native.None) in
                       let uu____10611 =
                         let uu____10620 =
                           let uu____10627 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10627, []) in
                         make_lower_bound uu____10620 lower_bounds in
                       (match uu____10611 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10639 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10639
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
                            ((let uu____10659 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10659
                              then
                                let wl' =
                                  let uu___156_10661 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___156_10661.wl_deferred);
                                    ctr = (uu___156_10661.ctr);
                                    defer_ok = (uu___156_10661.defer_ok);
                                    smt_ok = (uu___156_10661.smt_ok);
                                    tcenv = (uu___156_10661.tcenv)
                                  } in
                                let uu____10662 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10662
                              else ());
                             (let uu____10664 =
                                solve_t env eq_prob
                                  (let uu___157_10666 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___157_10666.wl_deferred);
                                     ctr = (uu___157_10666.ctr);
                                     defer_ok = (uu___157_10666.defer_ok);
                                     smt_ok = (uu___157_10666.smt_ok);
                                     tcenv = (uu___157_10666.tcenv)
                                   }) in
                              match uu____10664 with
                              | Success uu____10669 ->
                                  let wl1 =
                                    let uu___158_10671 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___158_10671.wl_deferred);
                                      ctr = (uu___158_10671.ctr);
                                      defer_ok = (uu___158_10671.defer_ok);
                                      smt_ok = (uu___158_10671.smt_ok);
                                      tcenv = (uu___158_10671.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10673 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10678 -> FStar_Pervasives_Native.None))))
              | uu____10679 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10688 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10688
         then
           let uu____10689 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10689
         else ());
        (let uu____10691 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10691 with
         | (u,args) ->
             let uu____10730 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____10730 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____10771 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____10771 with
                    | (h1,args1) ->
                        let uu____10812 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____10812 with
                         | (h2,uu____10832) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10859 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____10859
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____10877 =
                                          let uu____10880 =
                                            let uu____10881 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____10881 in
                                          [uu____10880] in
                                        FStar_Pervasives_Native.Some
                                          uu____10877))
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
                                       (let uu____10914 =
                                          let uu____10917 =
                                            let uu____10918 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____10918 in
                                          [uu____10917] in
                                        FStar_Pervasives_Native.Some
                                          uu____10914))
                                  else FStar_Pervasives_Native.None
                              | uu____10932 -> FStar_Pervasives_Native.None)) in
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
                             let uu____11022 =
                               let uu____11031 =
                                 let uu____11034 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____11034 in
                               (uu____11031, m1) in
                             FStar_Pervasives_Native.Some uu____11022)
                    | (uu____11047,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11049)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11097),uu____11098) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11145 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11198) ->
                       let uu____11223 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___130_11249  ->
                                 match uu___130_11249 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11256 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____11256 with
                                           | (u',uu____11272) ->
                                               let uu____11293 =
                                                 let uu____11294 =
                                                   whnf env u' in
                                                 uu____11294.FStar_Syntax_Syntax.n in
                                               (match uu____11293 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11298) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11323 -> false))
                                      | uu____11324 -> false)
                                 | uu____11327 -> false)) in
                       (match uu____11223 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11365 tps =
                              match uu____11365 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11427 =
                                         let uu____11438 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11438 in
                                       (match uu____11427 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11489 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11500 =
                              let uu____11511 =
                                let uu____11520 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11520, []) in
                              make_upper_bound uu____11511 upper_bounds in
                            (match uu____11500 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11534 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11534
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
                                 ((let uu____11560 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11560
                                   then
                                     let wl' =
                                       let uu___159_11562 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___159_11562.wl_deferred);
                                         ctr = (uu___159_11562.ctr);
                                         defer_ok = (uu___159_11562.defer_ok);
                                         smt_ok = (uu___159_11562.smt_ok);
                                         tcenv = (uu___159_11562.tcenv)
                                       } in
                                     let uu____11563 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11563
                                   else ());
                                  (let uu____11565 =
                                     solve_t env eq_prob
                                       (let uu___160_11567 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___160_11567.wl_deferred);
                                          ctr = (uu___160_11567.ctr);
                                          defer_ok =
                                            (uu___160_11567.defer_ok);
                                          smt_ok = (uu___160_11567.smt_ok);
                                          tcenv = (uu___160_11567.tcenv)
                                        }) in
                                   match uu____11565 with
                                   | Success uu____11570 ->
                                       let wl1 =
                                         let uu___161_11572 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___161_11572.wl_deferred);
                                           ctr = (uu___161_11572.ctr);
                                           defer_ok =
                                             (uu___161_11572.defer_ok);
                                           smt_ok = (uu___161_11572.smt_ok);
                                           tcenv = (uu___161_11572.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11574 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11579 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11580 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____11671 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11671
                      then
                        let uu____11672 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11672
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___162_11726 = hd1 in
                      let uu____11727 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___162_11726.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___162_11726.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11727
                      } in
                    let hd21 =
                      let uu___163_11731 = hd2 in
                      let uu____11732 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___163_11731.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___163_11731.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11732
                      } in
                    let prob =
                      let uu____11736 =
                        let uu____11741 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11741 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____11736 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11752 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11752 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11756 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____11756 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11786 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11791 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11786 uu____11791 in
                         ((let uu____11801 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11801
                           then
                             let uu____11802 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11803 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11802 uu____11803
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11826 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11836 = aux scope env [] bs1 bs2 in
              match uu____11836 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11860 = compress_tprob wl problem in
        solve_t' env uu____11860 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11893 = head_matches_delta env1 wl1 t1 t2 in
          match uu____11893 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____11924,uu____11925) ->
                   let may_relate head3 =
                     let uu____11950 =
                       let uu____11951 = FStar_Syntax_Util.un_uinst head3 in
                       uu____11951.FStar_Syntax_Syntax.n in
                     match uu____11950 with
                     | FStar_Syntax_Syntax.Tm_name uu____11954 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____11955 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____11979 -> false in
                   let uu____11980 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____11980
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
                                let uu____11997 =
                                  let uu____11998 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____11998 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____11997 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____12000 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____12000
                   else
                     (let uu____12002 =
                        let uu____12003 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____12004 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____12003 uu____12004 in
                      giveup env1 uu____12002 orig)
               | (uu____12005,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___164_12019 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___164_12019.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___164_12019.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___164_12019.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___164_12019.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___164_12019.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___164_12019.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___164_12019.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___164_12019.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____12020,FStar_Pervasives_Native.None ) ->
                   ((let uu____12032 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____12032
                     then
                       let uu____12033 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____12034 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____12035 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____12036 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____12033
                         uu____12034 uu____12035 uu____12036
                     else ());
                    (let uu____12038 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____12038 with
                     | (head11,args1) ->
                         let uu____12075 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____12075 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____12129 =
                                  let uu____12130 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____12131 = args_to_string args1 in
                                  let uu____12132 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____12133 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____12130 uu____12131 uu____12132
                                    uu____12133 in
                                giveup env1 uu____12129 orig
                              else
                                (let uu____12135 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____12141 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____12141 = FStar_Syntax_Util.Equal) in
                                 if uu____12135
                                 then
                                   let uu____12142 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____12142 with
                                   | USolved wl2 ->
                                       let uu____12144 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____12144
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____12148 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____12148 with
                                    | (base1,refinement1) ->
                                        let uu____12185 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____12185 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12266 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____12266 with
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
                                                           (fun uu____12288 
                                                              ->
                                                              fun uu____12289
                                                                 ->
                                                                match 
                                                                  (uu____12288,
                                                                    uu____12289)
                                                                with
                                                                | ((a,uu____12307),
                                                                   (a',uu____12309))
                                                                    ->
                                                                    let uu____12318
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
                                                                    uu____12318)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____12328 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12328 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12334 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___165_12382 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___165_12382.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___165_12382.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___165_12382.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___165_12382.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___165_12382.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___165_12382.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___165_12382.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___165_12382.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____12402 = p in
          match uu____12402 with
          | (((u,k),xs,c),ps,(h,uu____12413,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____12495 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____12495 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____12518 = h gs_xs in
                     let uu____12519 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57) in
                     FStar_Syntax_Util.abs xs1 uu____12518 uu____12519 in
                   ((let uu____12525 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____12525
                     then
                       let uu____12526 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____12527 = FStar_Syntax_Print.comp_to_string c in
                       let uu____12528 = FStar_Syntax_Print.term_to_string im in
                       let uu____12529 = FStar_Syntax_Print.tag_of_term im in
                       let uu____12530 =
                         let uu____12531 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____12531
                           (FStar_String.concat ", ") in
                       let uu____12536 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____12526 uu____12527 uu____12528 uu____12529
                         uu____12530 uu____12536
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___131_12557 =
          match uu___131_12557 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____12589 = p in
          match uu____12589 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____12680 = FStar_List.nth ps i in
              (match uu____12680 with
               | (pi,uu____12684) ->
                   let uu____12689 = FStar_List.nth xs i in
                   (match uu____12689 with
                    | (xi,uu____12701) ->
                        let rec gs k =
                          let uu____12714 = FStar_Syntax_Util.arrow_formals k in
                          match uu____12714 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____12801)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____12814 = new_uvar r xs k_a in
                                    (match uu____12814 with
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
                                         let uu____12836 = aux subst2 tl1 in
                                         (match uu____12836 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____12863 =
                                                let uu____12866 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____12866 :: gi_xs' in
                                              let uu____12867 =
                                                let uu____12870 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____12870 :: gi_ps' in
                                              (uu____12863, uu____12867))) in
                              aux [] bs in
                        let uu____12875 =
                          let uu____12876 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____12876 in
                        if uu____12875
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____12880 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____12880 with
                           | (g_xs,uu____12892) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____12903 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____12904 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58) in
                                 FStar_Syntax_Util.abs xs uu____12903
                                   uu____12904 in
                               let sub1 =
                                 let uu____12910 =
                                   let uu____12915 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____12918 =
                                     let uu____12921 =
                                       FStar_List.map
                                         (fun uu____12936  ->
                                            match uu____12936 with
                                            | (uu____12945,uu____12946,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____12921 in
                                   mk_problem (p_scope orig) orig uu____12915
                                     (p_rel orig) uu____12918
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____12910 in
                               ((let uu____12961 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____12961
                                 then
                                   let uu____12962 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____12963 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____12962 uu____12963
                                 else ());
                                (let wl2 =
                                   let uu____12966 =
                                     let uu____12969 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____12969 in
                                   solve_prob orig uu____12966
                                     [TERM (u, proj)] wl1 in
                                 let uu____12978 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____12978))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____13009 = lhs in
          match uu____13009 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____13045 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____13045 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____13078 =
                        let uu____13125 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____13125) in
                      FStar_Pervasives_Native.Some uu____13078
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____13269 =
                           let uu____13276 =
                             let uu____13277 = FStar_Syntax_Subst.compress k in
                             uu____13277.FStar_Syntax_Syntax.n in
                           (uu____13276, args) in
                         match uu____13269 with
                         | (uu____13288,[]) ->
                             let uu____13291 =
                               let uu____13302 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____13302) in
                             FStar_Pervasives_Native.Some uu____13291
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____13323,uu____13324) ->
                             let uu____13345 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____13345 with
                              | (uv1,uv_args) ->
                                  let uu____13388 =
                                    let uu____13389 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____13389.FStar_Syntax_Syntax.n in
                                  (match uu____13388 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____13399) ->
                                       let uu____13424 =
                                         pat_vars env [] uv_args in
                                       (match uu____13424 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____13451  ->
                                                      let uu____13452 =
                                                        let uu____13453 =
                                                          let uu____13454 =
                                                            let uu____13459 =
                                                              let uu____13460
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____13460
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____13459 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____13454 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____13453 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____13452)) in
                                            let c1 =
                                              let uu____13470 =
                                                let uu____13471 =
                                                  let uu____13476 =
                                                    let uu____13477 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____13477
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____13476 in
                                                FStar_Pervasives_Native.fst
                                                  uu____13471 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____13470 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____13490 =
                                                let uu____13493 =
                                                  let uu____13494 =
                                                    let uu____13497 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____13497
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____13494 in
                                                FStar_Pervasives_Native.Some
                                                  uu____13493 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____13490 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____13515 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____13520,uu____13521) ->
                             let uu____13540 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____13540 with
                              | (uv1,uv_args) ->
                                  let uu____13583 =
                                    let uu____13584 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____13584.FStar_Syntax_Syntax.n in
                                  (match uu____13583 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____13594) ->
                                       let uu____13619 =
                                         pat_vars env [] uv_args in
                                       (match uu____13619 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____13646  ->
                                                      let uu____13647 =
                                                        let uu____13648 =
                                                          let uu____13649 =
                                                            let uu____13654 =
                                                              let uu____13655
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____13655
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____13654 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____13649 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____13648 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____13647)) in
                                            let c1 =
                                              let uu____13665 =
                                                let uu____13666 =
                                                  let uu____13671 =
                                                    let uu____13672 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____13672
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____13671 in
                                                FStar_Pervasives_Native.fst
                                                  uu____13666 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____13665 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____13685 =
                                                let uu____13688 =
                                                  let uu____13689 =
                                                    let uu____13692 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____13692
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____13689 in
                                                FStar_Pervasives_Native.Some
                                                  uu____13688 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____13685 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____13710 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____13717) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____13758 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____13758
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____13794 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____13794 with
                                  | (args1,rest) ->
                                      let uu____13823 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____13823 with
                                       | (xs2,c2) ->
                                           let uu____13836 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____13836
                                             (fun uu____13860  ->
                                                match uu____13860 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____13900 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____13900 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____13968 =
                                        let uu____13973 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____13973 in
                                      FStar_All.pipe_right uu____13968
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____13988 ->
                             let uu____13995 =
                               let uu____13996 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____13997 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____13998 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____13996 uu____13997 uu____13998 in
                             failwith uu____13995 in
                       let uu____14005 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____14005
                         (fun uu____14060  ->
                            match uu____14060 with
                            | (xs1,c1) ->
                                let uu____14109 =
                                  let uu____14150 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____14150) in
                                FStar_Pervasives_Native.Some uu____14109)) in
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
                     let uu____14268 = imitate orig env wl1 st in
                     match uu____14268 with
                     | Failed uu____14273 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____14281 = project orig env wl1 i st in
                      match uu____14281 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____14289) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____14307 = FStar_Syntax_Util.head_and_args t21 in
                match uu____14307 with
                | (hd1,uu____14323) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____14344 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____14357 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____14358 -> true
                     | uu____14375 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____14379 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____14379
                         then true
                         else
                           ((let uu____14382 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____14382
                             then
                               let uu____14383 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____14383
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____14392 =
                    let uu____14395 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____14395
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____14392 FStar_Syntax_Free.names in
                let uu____14440 = FStar_Util.set_is_empty fvs_hd in
                if uu____14440
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____14451 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____14451 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____14464 =
                            let uu____14465 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____14465 in
                          giveup_or_defer1 orig uu____14464
                        else
                          (let uu____14467 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____14467
                           then
                             let uu____14468 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____14468
                              then
                                let uu____14469 = subterms args_lhs in
                                imitate' orig env wl1 uu____14469
                              else
                                ((let uu____14474 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____14474
                                  then
                                    let uu____14475 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____14476 = names_to_string fvs1 in
                                    let uu____14477 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____14475 uu____14476 uu____14477
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____14484 ->
                                        let uu____14485 = sn_binders env vars in
                                        u_abs k_uv uu____14485 t21 in
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
                               (let uu____14499 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____14499
                                then
                                  ((let uu____14501 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____14501
                                    then
                                      let uu____14502 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____14503 = names_to_string fvs1 in
                                      let uu____14504 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____14502 uu____14503 uu____14504
                                    else ());
                                   (let uu____14506 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs)
                                      uu____14506 (- (Prims.parse_int "1"))))
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
                     (let uu____14517 =
                        let uu____14518 = FStar_Syntax_Free.names t1 in
                        check_head uu____14518 t2 in
                      if uu____14517
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____14523 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____14523
                          then
                            let uu____14524 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____14524
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____14527 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____14527 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____14582 =
               match uu____14582 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k in
                   let uu____14632 = FStar_Syntax_Util.arrow_formals k1 in
                   (match uu____14632 with
                    | (all_formals,uu____14650) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____14813  ->
                                        match uu____14813 with
                                        | (x,imp) ->
                                            let uu____14824 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____14824, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____14837 = FStar_Syntax_Util.type_u () in
                                match uu____14837 with
                                | (t1,uu____14843) ->
                                    let uu____14844 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    FStar_Pervasives_Native.fst uu____14844 in
                              let uu____14849 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____14849 with
                               | (t',tm_u1) ->
                                   let uu____14860 = destruct_flex_t t' in
                                   (match uu____14860 with
                                    | (uu____14895,u1,k11,uu____14898) ->
                                        let sol =
                                          let uu____14944 =
                                            let uu____14953 =
                                              u_abs k1 all_formals t' in
                                            ((u, k1), uu____14953) in
                                          TERM uu____14944 in
                                        let t_app =
                                          FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                            pat_args1
                                            FStar_Pervasives_Native.None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____15053 = pat_var_opt env pat_args hd1 in
                              (match uu____15053 with
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
                                              (fun uu____15110  ->
                                                 match uu____15110 with
                                                 | (x,uu____15116) ->
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
                                      let uu____15125 =
                                        let uu____15126 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____15126 in
                                      if uu____15125
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____15132 =
                                           FStar_Util.set_add
                                             (FStar_Pervasives_Native.fst
                                                formal) pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____15132 formals1
                                           tl1)))
                          | uu____15143 -> failwith "Impossible" in
                        let uu____15164 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____15164 all_formals args) in
             let solve_both_pats wl1 uu____15229 uu____15230 r =
               match (uu____15229, uu____15230) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15428 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15428
                   then
                     let uu____15429 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15429
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15453 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15453
                       then
                         let uu____15454 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15455 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15456 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15457 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15458 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15454 uu____15455 uu____15456 uu____15457
                           uu____15458
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____15518 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____15518 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____15532 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____15532 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____15586 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____15586 in
                                  let uu____15589 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____15589 k3)
                           else
                             (let uu____15593 =
                                let uu____15594 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____15595 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____15596 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____15594 uu____15595 uu____15596 in
                              failwith uu____15593) in
                       let uu____15597 =
                         let uu____15606 =
                           let uu____15619 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____15619 in
                         match uu____15606 with
                         | (bs,k1') ->
                             let uu____15646 =
                               let uu____15659 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____15659 in
                             (match uu____15646 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____15689 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____15689 in
                                  let uu____15698 =
                                    let uu____15703 =
                                      let uu____15704 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____15704.FStar_Syntax_Syntax.n in
                                    let uu____15707 =
                                      let uu____15708 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____15708.FStar_Syntax_Syntax.n in
                                    (uu____15703, uu____15707) in
                                  (match uu____15698 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____15719,uu____15720) ->
                                       (k1', [sub_prob])
                                   | (uu____15725,FStar_Syntax_Syntax.Tm_type
                                      uu____15726) -> (k2', [sub_prob])
                                   | uu____15731 ->
                                       let uu____15736 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____15736 with
                                        | (t,uu____15750) ->
                                            let uu____15751 = new_uvar r zs t in
                                            (match uu____15751 with
                                             | (k_zs,uu____15765) ->
                                                 let kprob =
                                                   let uu____15767 =
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
                                                          _0_64) uu____15767 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____15597 with
                       | (k_u',sub_probs) ->
                           let uu____15788 =
                             let uu____15799 =
                               let uu____15800 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____15800 in
                             let uu____15809 =
                               let uu____15812 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____15812 in
                             let uu____15815 =
                               let uu____15818 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____15818 in
                             (uu____15799, uu____15809, uu____15815) in
                           (match uu____15788 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____15837 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____15837 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____15856 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____15856
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____15860 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____15860 with
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
             let solve_one_pat uu____15913 uu____15914 =
               match (uu____15913, uu____15914) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16032 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____16032
                     then
                       let uu____16033 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____16034 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16033 uu____16034
                     else ());
                    (let uu____16036 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____16036
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16055  ->
                              fun uu____16056  ->
                                match (uu____16055, uu____16056) with
                                | ((a,uu____16074),(t21,uu____16076)) ->
                                    let uu____16085 =
                                      let uu____16090 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16090
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16085
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2 in
                       let guard =
                         let uu____16096 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16096 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16111 = occurs_check env wl (u1, k1) t21 in
                        match uu____16111 with
                        | (occurs_ok,uu____16119) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16127 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16127
                            then
                              let sol =
                                let uu____16129 =
                                  let uu____16138 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16138) in
                                TERM uu____16129 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16145 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16145
                               then
                                 let uu____16146 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16146 with
                                 | (sol,(uu____16164,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16178 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16178
                                       then
                                         let uu____16179 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16179
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16186 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16188 = lhs in
             match uu____16188 with
             | (t1,u1,k1,args1) ->
                 let uu____16193 = rhs in
                 (match uu____16193 with
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
                       | uu____16233 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16243 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16243 with
                              | (sol,uu____16255) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16258 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16258
                                    then
                                      let uu____16259 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16259
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16266 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16268 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16268
        then
          let uu____16269 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16269
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16273 = FStar_Util.physical_equality t1 t2 in
           if uu____16273
           then
             let uu____16274 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16274
           else
             ((let uu____16277 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16277
               then
                 let uu____16278 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16278
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____16281,uu____16282) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16283,FStar_Syntax_Syntax.Tm_bvar uu____16284) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___132_16339 =
                     match uu___132_16339 with
                     | [] -> c
                     | bs ->
                         let uu____16361 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16361 in
                   let uu____16370 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16370 with
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
                                   let uu____16512 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____16512
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____16514 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____16514))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___133_16590 =
                     match uu___133_16590 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____16624 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____16624 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____16760 =
                                   let uu____16765 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____16766 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____16765
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____16766 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____16760))
               | (FStar_Syntax_Syntax.Tm_abs uu____16771,uu____16772) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____16797 -> true
                     | uu____16814 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____16848 =
                     let uu____16865 = maybe_eta t1 in
                     let uu____16872 = maybe_eta t2 in
                     (uu____16865, uu____16872) in
                   (match uu____16848 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_16914 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_16914.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_16914.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_16914.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_16914.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_16914.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_16914.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_16914.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_16914.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____16937 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____16937
                        then
                          let uu____16938 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____16938 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____16966 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____16966
                        then
                          let uu____16967 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____16967 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____16975 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____16992,FStar_Syntax_Syntax.Tm_abs uu____16993) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17018 -> true
                     | uu____17035 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____17069 =
                     let uu____17086 = maybe_eta t1 in
                     let uu____17093 = maybe_eta t2 in
                     (uu____17086, uu____17093) in
                   (match uu____17069 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_17135 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_17135.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_17135.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_17135.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_17135.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_17135.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_17135.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_17135.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_17135.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17158 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17158
                        then
                          let uu____17159 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17159 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17187 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17187
                        then
                          let uu____17188 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17188 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____17196 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____17213,FStar_Syntax_Syntax.Tm_refine uu____17214) ->
                   let uu____17227 = as_refinement env wl t1 in
                   (match uu____17227 with
                    | (x1,phi1) ->
                        let uu____17234 = as_refinement env wl t2 in
                        (match uu____17234 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____17242 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____17242 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____17280 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____17280
                                 (guard_on_element wl problem x11) in
                             let fallback uu____17284 =
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
                                 let uu____17290 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____17290 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____17299 =
                                   let uu____17304 =
                                     let uu____17305 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____17305 :: (p_scope orig) in
                                   mk_problem uu____17304 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____17299 in
                               let uu____17310 =
                                 solve env1
                                   (let uu___167_17312 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___167_17312.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___167_17312.smt_ok);
                                      tcenv = (uu___167_17312.tcenv)
                                    }) in
                               (match uu____17310 with
                                | Failed uu____17319 -> fallback ()
                                | Success uu____17324 ->
                                    let guard =
                                      let uu____17328 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____17333 =
                                        let uu____17334 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____17334
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____17328
                                        uu____17333 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___168_17343 = wl1 in
                                      {
                                        attempting =
                                          (uu___168_17343.attempting);
                                        wl_deferred =
                                          (uu___168_17343.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___168_17343.defer_ok);
                                        smt_ok = (uu___168_17343.smt_ok);
                                        tcenv = (uu___168_17343.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17345,FStar_Syntax_Syntax.Tm_uvar uu____17346) ->
                   let uu____17379 = destruct_flex_t t1 in
                   let uu____17380 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17379 uu____17380
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17381;
                     FStar_Syntax_Syntax.pos = uu____17382;
                     FStar_Syntax_Syntax.vars = uu____17383;_},uu____17384),FStar_Syntax_Syntax.Tm_uvar
                  uu____17385) ->
                   let uu____17438 = destruct_flex_t t1 in
                   let uu____17439 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17438 uu____17439
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17440,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17441;
                     FStar_Syntax_Syntax.pos = uu____17442;
                     FStar_Syntax_Syntax.vars = uu____17443;_},uu____17444))
                   ->
                   let uu____17497 = destruct_flex_t t1 in
                   let uu____17498 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17497 uu____17498
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17499;
                     FStar_Syntax_Syntax.pos = uu____17500;
                     FStar_Syntax_Syntax.vars = uu____17501;_},uu____17502),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17503;
                     FStar_Syntax_Syntax.pos = uu____17504;
                     FStar_Syntax_Syntax.vars = uu____17505;_},uu____17506))
                   ->
                   let uu____17579 = destruct_flex_t t1 in
                   let uu____17580 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17579 uu____17580
               | (FStar_Syntax_Syntax.Tm_uvar uu____17581,uu____17582) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____17599 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____17599 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17606;
                     FStar_Syntax_Syntax.pos = uu____17607;
                     FStar_Syntax_Syntax.vars = uu____17608;_},uu____17609),uu____17610)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____17647 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____17647 t2 wl
               | (uu____17654,FStar_Syntax_Syntax.Tm_uvar uu____17655) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____17672,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17673;
                     FStar_Syntax_Syntax.pos = uu____17674;
                     FStar_Syntax_Syntax.vars = uu____17675;_},uu____17676))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17713,FStar_Syntax_Syntax.Tm_type uu____17714) ->
                   solve_t' env
                     (let uu___169_17732 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_17732.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_17732.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_17732.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_17732.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_17732.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_17732.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_17732.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_17732.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_17732.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17733;
                     FStar_Syntax_Syntax.pos = uu____17734;
                     FStar_Syntax_Syntax.vars = uu____17735;_},uu____17736),FStar_Syntax_Syntax.Tm_type
                  uu____17737) ->
                   solve_t' env
                     (let uu___169_17775 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_17775.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_17775.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_17775.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_17775.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_17775.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_17775.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_17775.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_17775.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_17775.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17776,FStar_Syntax_Syntax.Tm_arrow uu____17777) ->
                   solve_t' env
                     (let uu___169_17807 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_17807.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_17807.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_17807.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_17807.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_17807.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_17807.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_17807.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_17807.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_17807.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17808;
                     FStar_Syntax_Syntax.pos = uu____17809;
                     FStar_Syntax_Syntax.vars = uu____17810;_},uu____17811),FStar_Syntax_Syntax.Tm_arrow
                  uu____17812) ->
                   solve_t' env
                     (let uu___169_17862 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_17862.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_17862.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_17862.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_17862.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_17862.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_17862.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_17862.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_17862.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_17862.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____17863,uu____17864) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____17883 =
                        let uu____17884 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____17884 in
                      if uu____17883
                      then
                        let uu____17885 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___170_17891 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_17891.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_17891.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_17891.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_17891.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_17891.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_17891.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_17891.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_17891.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_17891.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____17892 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____17885 uu____17892 t2
                          wl
                      else
                        (let uu____17900 = base_and_refinement env wl t2 in
                         match uu____17900 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____17943 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___171_17949 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_17949.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_17949.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_17949.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_17949.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_17949.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_17949.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_17949.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_17949.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_17949.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____17950 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____17943
                                    uu____17950 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___172_17970 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_17970.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_17970.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____17973 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____17973 in
                                  let guard =
                                    let uu____17985 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____17985
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17993;
                     FStar_Syntax_Syntax.pos = uu____17994;
                     FStar_Syntax_Syntax.vars = uu____17995;_},uu____17996),uu____17997)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18036 =
                        let uu____18037 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18037 in
                      if uu____18036
                      then
                        let uu____18038 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___170_18044 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_18044.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_18044.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_18044.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_18044.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_18044.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_18044.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_18044.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_18044.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_18044.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18045 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18038 uu____18045 t2
                          wl
                      else
                        (let uu____18053 = base_and_refinement env wl t2 in
                         match uu____18053 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18096 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___171_18102 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_18102.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_18102.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_18102.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_18102.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_18102.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_18102.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_18102.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_18102.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_18102.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18103 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18096
                                    uu____18103 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___172_18123 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_18123.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_18123.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18126 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____18126 in
                                  let guard =
                                    let uu____18138 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18138
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18146,FStar_Syntax_Syntax.Tm_uvar uu____18147) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18165 = base_and_refinement env wl t1 in
                      match uu____18165 with
                      | (t_base,uu____18181) ->
                          solve_t env
                            (let uu___173_18203 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_18203.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_18203.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_18203.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_18203.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_18203.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_18203.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_18203.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_18203.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18206,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18207;
                     FStar_Syntax_Syntax.pos = uu____18208;
                     FStar_Syntax_Syntax.vars = uu____18209;_},uu____18210))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18248 = base_and_refinement env wl t1 in
                      match uu____18248 with
                      | (t_base,uu____18264) ->
                          solve_t env
                            (let uu___173_18286 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_18286.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_18286.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_18286.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_18286.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_18286.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_18286.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_18286.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_18286.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18289,uu____18290) ->
                   let t21 =
                     let uu____18300 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____18300 in
                   solve_t env
                     (let uu___174_18324 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_18324.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___174_18324.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___174_18324.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___174_18324.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_18324.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_18324.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_18324.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_18324.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_18324.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____18325,FStar_Syntax_Syntax.Tm_refine uu____18326) ->
                   let t11 =
                     let uu____18336 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____18336 in
                   solve_t env
                     (let uu___175_18360 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_18360.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_18360.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_18360.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_18360.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_18360.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_18360.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_18360.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_18360.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_18360.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____18363,uu____18364) ->
                   let head1 =
                     let uu____18390 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18390
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18434 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18434
                       FStar_Pervasives_Native.fst in
                   let uu____18475 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18475
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18490 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18490
                      then
                        let guard =
                          let uu____18502 =
                            let uu____18503 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18503 = FStar_Syntax_Util.Equal in
                          if uu____18502
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18507 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____18507) in
                        let uu____18510 = solve_prob orig guard [] wl in
                        solve env uu____18510
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____18513,uu____18514) ->
                   let head1 =
                     let uu____18524 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18524
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18568 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18568
                       FStar_Pervasives_Native.fst in
                   let uu____18609 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18609
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18624 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18624
                      then
                        let guard =
                          let uu____18636 =
                            let uu____18637 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18637 = FStar_Syntax_Util.Equal in
                          if uu____18636
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18641 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____18641) in
                        let uu____18644 = solve_prob orig guard [] wl in
                        solve env uu____18644
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____18647,uu____18648) ->
                   let head1 =
                     let uu____18652 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18652
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18696 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18696
                       FStar_Pervasives_Native.fst in
                   let uu____18737 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18737
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18752 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18752
                      then
                        let guard =
                          let uu____18764 =
                            let uu____18765 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18765 = FStar_Syntax_Util.Equal in
                          if uu____18764
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18769 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____18769) in
                        let uu____18772 = solve_prob orig guard [] wl in
                        solve env uu____18772
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____18775,uu____18776) ->
                   let head1 =
                     let uu____18780 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18780
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18824 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18824
                       FStar_Pervasives_Native.fst in
                   let uu____18865 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18865
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18880 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18880
                      then
                        let guard =
                          let uu____18892 =
                            let uu____18893 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18893 = FStar_Syntax_Util.Equal in
                          if uu____18892
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18897 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____18897) in
                        let uu____18900 = solve_prob orig guard [] wl in
                        solve env uu____18900
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____18903,uu____18904) ->
                   let head1 =
                     let uu____18908 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18908
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18952 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18952
                       FStar_Pervasives_Native.fst in
                   let uu____18993 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18993
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19008 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19008
                      then
                        let guard =
                          let uu____19020 =
                            let uu____19021 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19021 = FStar_Syntax_Util.Equal in
                          if uu____19020
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19025 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19025) in
                        let uu____19028 = solve_prob orig guard [] wl in
                        solve env uu____19028
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19031,uu____19032) ->
                   let head1 =
                     let uu____19050 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19050
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19094 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19094
                       FStar_Pervasives_Native.fst in
                   let uu____19135 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19135
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19150 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19150
                      then
                        let guard =
                          let uu____19162 =
                            let uu____19163 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19163 = FStar_Syntax_Util.Equal in
                          if uu____19162
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19167 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19167) in
                        let uu____19170 = solve_prob orig guard [] wl in
                        solve env uu____19170
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19173,FStar_Syntax_Syntax.Tm_match uu____19174) ->
                   let head1 =
                     let uu____19200 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19200
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19244 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19244
                       FStar_Pervasives_Native.fst in
                   let uu____19285 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19285
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19300 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19300
                      then
                        let guard =
                          let uu____19312 =
                            let uu____19313 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19313 = FStar_Syntax_Util.Equal in
                          if uu____19312
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19317 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19317) in
                        let uu____19320 = solve_prob orig guard [] wl in
                        solve env uu____19320
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19323,FStar_Syntax_Syntax.Tm_uinst uu____19324) ->
                   let head1 =
                     let uu____19334 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19334
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19378 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19378
                       FStar_Pervasives_Native.fst in
                   let uu____19419 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19419
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19434 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19434
                      then
                        let guard =
                          let uu____19446 =
                            let uu____19447 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19447 = FStar_Syntax_Util.Equal in
                          if uu____19446
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19451 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____19451) in
                        let uu____19454 = solve_prob orig guard [] wl in
                        solve env uu____19454
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19457,FStar_Syntax_Syntax.Tm_name uu____19458) ->
                   let head1 =
                     let uu____19462 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19462
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19506 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19506
                       FStar_Pervasives_Native.fst in
                   let uu____19547 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19547
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19562 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19562
                      then
                        let guard =
                          let uu____19574 =
                            let uu____19575 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19575 = FStar_Syntax_Util.Equal in
                          if uu____19574
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19579 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____19579) in
                        let uu____19582 = solve_prob orig guard [] wl in
                        solve env uu____19582
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19585,FStar_Syntax_Syntax.Tm_constant uu____19586) ->
                   let head1 =
                     let uu____19590 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19590
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19634 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19634
                       FStar_Pervasives_Native.fst in
                   let uu____19675 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19675
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19690 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19690
                      then
                        let guard =
                          let uu____19702 =
                            let uu____19703 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19703 = FStar_Syntax_Util.Equal in
                          if uu____19702
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19707 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____19707) in
                        let uu____19710 = solve_prob orig guard [] wl in
                        solve env uu____19710
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19713,FStar_Syntax_Syntax.Tm_fvar uu____19714) ->
                   let head1 =
                     let uu____19718 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19718
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19762 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19762
                       FStar_Pervasives_Native.fst in
                   let uu____19803 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19803
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19818 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19818
                      then
                        let guard =
                          let uu____19830 =
                            let uu____19831 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19831 = FStar_Syntax_Util.Equal in
                          if uu____19830
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19835 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____19835) in
                        let uu____19838 = solve_prob orig guard [] wl in
                        solve env uu____19838
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19841,FStar_Syntax_Syntax.Tm_app uu____19842) ->
                   let head1 =
                     let uu____19860 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19860
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19904 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19904
                       FStar_Pervasives_Native.fst in
                   let uu____19945 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19945
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19960 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19960
                      then
                        let guard =
                          let uu____19972 =
                            let uu____19973 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19973 = FStar_Syntax_Util.Equal in
                          if uu____19972
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19977 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____19977) in
                        let uu____19980 = solve_prob orig guard [] wl in
                        solve env uu____19980
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____19984,uu____19985),uu____19986) ->
                   solve_t' env
                     (let uu___176_20028 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_20028.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___176_20028.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___176_20028.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___176_20028.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_20028.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_20028.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_20028.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_20028.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_20028.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____20031,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____20033,uu____20034)) ->
                   solve_t' env
                     (let uu___177_20076 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___177_20076.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___177_20076.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___177_20076.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___177_20076.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___177_20076.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___177_20076.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___177_20076.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___177_20076.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___177_20076.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____20077,uu____20078) ->
                   let uu____20091 =
                     let uu____20092 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20093 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20092
                       uu____20093 in
                   failwith uu____20091
               | (FStar_Syntax_Syntax.Tm_meta uu____20094,uu____20095) ->
                   let uu____20102 =
                     let uu____20103 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20104 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20103
                       uu____20104 in
                   failwith uu____20102
               | (FStar_Syntax_Syntax.Tm_delayed uu____20105,uu____20106) ->
                   let uu____20131 =
                     let uu____20132 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20133 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20132
                       uu____20133 in
                   failwith uu____20131
               | (uu____20134,FStar_Syntax_Syntax.Tm_meta uu____20135) ->
                   let uu____20142 =
                     let uu____20143 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20144 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20143
                       uu____20144 in
                   failwith uu____20142
               | (uu____20145,FStar_Syntax_Syntax.Tm_delayed uu____20146) ->
                   let uu____20171 =
                     let uu____20172 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20173 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20172
                       uu____20173 in
                   failwith uu____20171
               | (uu____20174,FStar_Syntax_Syntax.Tm_let uu____20175) ->
                   let uu____20188 =
                     let uu____20189 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20190 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20189
                       uu____20190 in
                   failwith uu____20188
               | uu____20191 -> giveup env "head tag mismatch" orig)))
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
          (let uu____20227 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20227
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____20247  ->
                  fun uu____20248  ->
                    match (uu____20247, uu____20248) with
                    | ((a1,uu____20266),(a2,uu____20268)) ->
                        let uu____20277 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_88  -> FStar_TypeChecker_Common.TProb _0_88)
                          uu____20277)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____20287 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p)
                      FStar_Pervasives_Native.fst) sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____20287 in
           let wl1 =
             solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20311 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20318)::[] -> wp1
              | uu____20335 ->
                  let uu____20344 =
                    let uu____20345 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20345 in
                  failwith uu____20344 in
            let uu____20348 =
              let uu____20357 =
                let uu____20358 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20358 in
              [uu____20357] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20348;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20359 = lift_c1 () in solve_eq uu____20359 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___134_20365  ->
                       match uu___134_20365 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20366 -> false)) in
             let uu____20367 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20401)::uu____20402,(wp2,uu____20404)::uu____20405)
                   -> (wp1, wp2)
               | uu____20462 ->
                   let uu____20483 =
                     let uu____20484 =
                       let uu____20489 =
                         let uu____20490 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____20491 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____20490 uu____20491 in
                       (uu____20489, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____20484 in
                   raise uu____20483 in
             match uu____20367 with
             | (wpc1,wpc2) ->
                 let uu____20510 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____20510
                 then
                   let uu____20513 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____20513 wl
                 else
                   (let uu____20517 =
                      let uu____20524 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____20524 in
                    match uu____20517 with
                    | (c2_decl,qualifiers) ->
                        let uu____20545 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____20545
                        then
                          let c1_repr =
                            let uu____20549 =
                              let uu____20550 =
                                let uu____20551 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____20551 in
                              let uu____20552 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20550 uu____20552 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____20549 in
                          let c2_repr =
                            let uu____20554 =
                              let uu____20555 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____20556 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20555 uu____20556 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____20554 in
                          let prob =
                            let uu____20558 =
                              let uu____20563 =
                                let uu____20564 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____20565 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____20564
                                  uu____20565 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____20563 in
                            FStar_TypeChecker_Common.TProb uu____20558 in
                          let wl1 =
                            let uu____20567 =
                              let uu____20570 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____20570 in
                            solve_prob orig uu____20567 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____20579 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____20579
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____20581 =
                                     let uu____20584 =
                                       let uu____20585 =
                                         let uu____20600 =
                                           let uu____20601 =
                                             let uu____20602 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____20602] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____20601 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____20603 =
                                           let uu____20606 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____20607 =
                                             let uu____20610 =
                                               let uu____20611 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20611 in
                                             [uu____20610] in
                                           uu____20606 :: uu____20607 in
                                         (uu____20600, uu____20603) in
                                       FStar_Syntax_Syntax.Tm_app uu____20585 in
                                     FStar_Syntax_Syntax.mk uu____20584 in
                                   uu____20581 FStar_Pervasives_Native.None r))
                               else
                                 (let uu____20618 =
                                    let uu____20621 =
                                      let uu____20622 =
                                        let uu____20637 =
                                          let uu____20638 =
                                            let uu____20639 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____20639] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____20638 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____20640 =
                                          let uu____20643 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____20644 =
                                            let uu____20647 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____20648 =
                                              let uu____20651 =
                                                let uu____20652 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20652 in
                                              [uu____20651] in
                                            uu____20647 :: uu____20648 in
                                          uu____20643 :: uu____20644 in
                                        (uu____20637, uu____20640) in
                                      FStar_Syntax_Syntax.Tm_app uu____20622 in
                                    FStar_Syntax_Syntax.mk uu____20621 in
                                  uu____20618 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____20659 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____20659 in
                           let wl1 =
                             let uu____20669 =
                               let uu____20672 =
                                 let uu____20675 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____20675 g in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____20672 in
                             solve_prob orig uu____20669 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____20688 = FStar_Util.physical_equality c1 c2 in
        if uu____20688
        then
          let uu____20689 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____20689
        else
          ((let uu____20692 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____20692
            then
              let uu____20693 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____20694 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20693
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20694
            else ());
           (let uu____20696 =
              let uu____20701 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____20702 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____20701, uu____20702) in
            match uu____20696 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20706),FStar_Syntax_Syntax.Total
                    (t2,uu____20708)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____20725 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20725 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20728,FStar_Syntax_Syntax.Total uu____20729) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20747),FStar_Syntax_Syntax.Total
                    (t2,uu____20749)) ->
                     let uu____20766 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20766 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20770),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20772)) ->
                     let uu____20789 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20789 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20793),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20795)) ->
                     let uu____20812 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20812 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20815,FStar_Syntax_Syntax.Comp uu____20816) ->
                     let uu____20825 =
                       let uu___178_20830 = problem in
                       let uu____20835 =
                         let uu____20836 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20836 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_20830.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20835;
                         FStar_TypeChecker_Common.relation =
                           (uu___178_20830.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___178_20830.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___178_20830.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_20830.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_20830.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_20830.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_20830.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_20830.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20825 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____20837,FStar_Syntax_Syntax.Comp uu____20838) ->
                     let uu____20847 =
                       let uu___178_20852 = problem in
                       let uu____20857 =
                         let uu____20858 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20858 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_20852.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20857;
                         FStar_TypeChecker_Common.relation =
                           (uu___178_20852.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___178_20852.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___178_20852.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_20852.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_20852.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_20852.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_20852.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_20852.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20847 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20859,FStar_Syntax_Syntax.GTotal uu____20860) ->
                     let uu____20869 =
                       let uu___179_20874 = problem in
                       let uu____20879 =
                         let uu____20880 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20880 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_20874.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___179_20874.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___179_20874.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20879;
                         FStar_TypeChecker_Common.element =
                           (uu___179_20874.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_20874.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_20874.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_20874.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_20874.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_20874.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20869 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20881,FStar_Syntax_Syntax.Total uu____20882) ->
                     let uu____20891 =
                       let uu___179_20896 = problem in
                       let uu____20901 =
                         let uu____20902 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20902 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_20896.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___179_20896.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___179_20896.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20901;
                         FStar_TypeChecker_Common.element =
                           (uu___179_20896.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_20896.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_20896.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_20896.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_20896.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_20896.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20891 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20903,FStar_Syntax_Syntax.Comp uu____20904) ->
                     let uu____20905 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____20905
                     then
                       let uu____20906 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____20906 wl
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
                           (let uu____20916 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____20916
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____20918 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____20918 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____20921 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____20923 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____20923) in
                                if uu____20921
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
                                  (let uu____20926 =
                                     let uu____20927 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____20928 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____20927 uu____20928 in
                                   giveup env uu____20926 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____20934 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____20972  ->
              match uu____20972 with
              | (uu____20985,uu____20986,u,uu____20988,uu____20989,uu____20990)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____20934 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21022 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21022 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21040 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21068  ->
                match uu____21068 with
                | (u1,u2) ->
                    let uu____21075 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21076 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21075 uu____21076)) in
      FStar_All.pipe_right uu____21040 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21095,[])) -> "{}"
      | uu____21120 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21137 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21137
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21140 =
              FStar_List.map
                (fun uu____21150  ->
                   match uu____21150 with
                   | (uu____21155,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21140 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21160 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21160 imps
let new_t_problem:
  'Auu____21175 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21175 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21175)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21209 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21209
                then
                  let uu____21210 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21211 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21210
                    (rel_to_string rel) uu____21211
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
            let uu____21239 =
              let uu____21242 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____21242 in
            FStar_Syntax_Syntax.new_bv uu____21239 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21251 =
              let uu____21254 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____21254 in
            let uu____21257 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21251 uu____21257 in
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
          let uu____21290 = FStar_Options.eager_inference () in
          if uu____21290
          then
            let uu___180_21291 = probs in
            {
              attempting = (uu___180_21291.attempting);
              wl_deferred = (uu___180_21291.wl_deferred);
              ctr = (uu___180_21291.ctr);
              defer_ok = false;
              smt_ok = (uu___180_21291.smt_ok);
              tcenv = (uu___180_21291.tcenv)
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
             (let uu____21303 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21303
              then
                let uu____21304 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21304
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
          ((let uu____21316 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21316
            then
              let uu____21317 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21317
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f in
            (let uu____21321 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21321
             then
               let uu____21322 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21322
             else ());
            (let f2 =
               let uu____21325 =
                 let uu____21326 = FStar_Syntax_Util.unmeta f1 in
                 uu____21326.FStar_Syntax_Syntax.n in
               match uu____21325 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21330 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___181_21331 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___181_21331.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_21331.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_21331.FStar_TypeChecker_Env.implicits)
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
            let uu____21353 =
              let uu____21354 =
                let uu____21355 =
                  let uu____21356 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21356
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21355;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21354 in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____21353
let with_guard_no_simp:
  'Auu____21387 .
    'Auu____21387 ->
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
            let uu____21407 =
              let uu____21408 =
                let uu____21409 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____21409
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
              {
                FStar_TypeChecker_Env.guard_f = uu____21408;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____21407
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
          (let uu____21451 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21451
           then
             let uu____21452 = FStar_Syntax_Print.term_to_string t1 in
             let uu____21453 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21452
               uu____21453
           else ());
          (let prob =
             let uu____21456 =
               let uu____21461 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____21461 in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____21456 in
           let g =
             let uu____21469 =
               let uu____21472 = singleton' env prob smt_ok in
               solve_and_commit env uu____21472
                 (fun uu____21474  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____21469 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21495 = try_teq true env t1 t2 in
        match uu____21495 with
        | FStar_Pervasives_Native.None  ->
            let uu____21498 =
              let uu____21499 =
                let uu____21504 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____21505 = FStar_TypeChecker_Env.get_range env in
                (uu____21504, uu____21505) in
              FStar_Errors.Error uu____21499 in
            raise uu____21498
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21508 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____21508
              then
                let uu____21509 = FStar_Syntax_Print.term_to_string t1 in
                let uu____21510 = FStar_Syntax_Print.term_to_string t2 in
                let uu____21511 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21509
                  uu____21510 uu____21511
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
          (let uu____21532 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21532
           then
             let uu____21533 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____21534 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____21533
               uu____21534
           else ());
          (let uu____21536 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____21536 with
           | (prob,x) ->
               let g =
                 let uu____21548 =
                   let uu____21551 = singleton' env prob smt_ok in
                   solve_and_commit env uu____21551
                     (fun uu____21553  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____21548 in
               ((let uu____21563 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____21563
                 then
                   let uu____21564 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____21565 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____21566 =
                     let uu____21567 = FStar_Util.must g in
                     guard_to_string env uu____21567 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____21564 uu____21565 uu____21566
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
          let uu____21599 = FStar_TypeChecker_Env.get_range env in
          let uu____21600 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____21599 uu____21600
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____21616 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____21616
         then
           let uu____21617 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____21618 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____21617
             uu____21618
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____21623 =
             let uu____21628 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____21628 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____21623 in
         let uu____21633 =
           let uu____21636 = singleton env prob in
           solve_and_commit env uu____21636
             (fun uu____21638  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____21633)
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
      fun uu____21670  ->
        match uu____21670 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____21709 =
                 let uu____21710 =
                   let uu____21715 =
                     let uu____21716 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____21717 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____21716 uu____21717 in
                   let uu____21718 = FStar_TypeChecker_Env.get_range env in
                   (uu____21715, uu____21718) in
                 FStar_Errors.Error uu____21710 in
               raise uu____21709) in
            let equiv1 v1 v' =
              let uu____21726 =
                let uu____21731 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____21732 = FStar_Syntax_Subst.compress_univ v' in
                (uu____21731, uu____21732) in
              match uu____21726 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____21751 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____21781 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____21781 with
                      | FStar_Syntax_Syntax.U_unif uu____21788 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____21817  ->
                                    match uu____21817 with
                                    | (u,v') ->
                                        let uu____21826 = equiv1 v1 v' in
                                        if uu____21826
                                        then
                                          let uu____21829 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____21829 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____21845 -> [])) in
            let uu____21850 =
              let wl =
                let uu___182_21854 = empty_worklist env in
                {
                  attempting = (uu___182_21854.attempting);
                  wl_deferred = (uu___182_21854.wl_deferred);
                  ctr = (uu___182_21854.ctr);
                  defer_ok = false;
                  smt_ok = (uu___182_21854.smt_ok);
                  tcenv = (uu___182_21854.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____21872  ->
                      match uu____21872 with
                      | (lb,v1) ->
                          let uu____21879 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____21879 with
                           | USolved wl1 -> ()
                           | uu____21881 -> fail lb v1))) in
            let rec check_ineq uu____21889 =
              match uu____21889 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____21898) -> true
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
                      uu____21921,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____21923,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____21934) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____21941,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____21949 -> false) in
            let uu____21954 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____21969  ->
                      match uu____21969 with
                      | (u,v1) ->
                          let uu____21976 = check_ineq (u, v1) in
                          if uu____21976
                          then true
                          else
                            ((let uu____21979 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____21979
                              then
                                let uu____21980 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____21981 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____21980
                                  uu____21981
                              else ());
                             false))) in
            if uu____21954
            then ()
            else
              ((let uu____21985 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____21985
                then
                  ((let uu____21987 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____21987);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____21997 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____21997))
                else ());
               (let uu____22007 =
                  let uu____22008 =
                    let uu____22013 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____22013) in
                  FStar_Errors.Error uu____22008 in
                raise uu____22007))
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
      let fail uu____22065 =
        match uu____22065 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22079 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22079
       then
         let uu____22080 = wl_to_string wl in
         let uu____22081 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22080 uu____22081
       else ());
      (let g1 =
         let uu____22096 = solve_and_commit env wl fail in
         match uu____22096 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___183_22109 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___183_22109.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___183_22109.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___183_22109.FStar_TypeChecker_Env.implicits)
             }
         | uu____22114 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___184_22118 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___184_22118.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___184_22118.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___184_22118.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22135 = FStar_ST.read last_proof_ns in
    match uu____22135 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.write last_proof_ns (FStar_Pervasives_Native.Some pns)
    | FStar_Pervasives_Native.Some old ->
        if old = pns
        then ()
        else
          ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           FStar_ST.write last_proof_ns (FStar_Pervasives_Native.Some pns))
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
            let uu___185_22178 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___185_22178.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___185_22178.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___185_22178.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22179 =
            let uu____22180 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22180 in
          if uu____22179
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____22188 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____22188
                   then
                     let uu____22189 = FStar_TypeChecker_Env.get_range env in
                     let uu____22190 =
                       let uu____22191 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22191 in
                     FStar_Errors.diag uu____22189 uu____22190
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   let uu____22194 = check_trivial vc1 in
                   match uu____22194 with
                   | FStar_TypeChecker_Common.Trivial  ->
                       FStar_Pervasives_Native.Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then
                         ((let uu____22201 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____22201
                           then
                             let uu____22202 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____22203 =
                               let uu____22204 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1
                                 "Cannot solve without SMT : %s\n"
                                 uu____22204 in
                             FStar_Errors.diag uu____22202 uu____22203
                           else ());
                          FStar_Pervasives_Native.None)
                       else
                         ((let uu____22209 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____22209
                           then
                             let uu____22210 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____22211 =
                               let uu____22212 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____22212 in
                             FStar_Errors.diag uu____22210 uu____22211
                           else ());
                          (let vcs =
                             let uu____22223 = FStar_Options.use_tactics () in
                             if uu____22223
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else
                               (let uu____22233 =
                                  let uu____22240 = FStar_Options.peek () in
                                  (env, vc2, uu____22240) in
                                [uu____22233]) in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____22274  ->
                                   match uu____22274 with
                                   | (env1,goal,opts) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify;
                                           FStar_TypeChecker_Normalize.Primops]
                                           env1 goal in
                                       let uu____22285 = check_trivial goal1 in
                                       (match uu____22285 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____22287 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____22287
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            (FStar_Options.push ();
                                             FStar_Options.set opts;
                                             maybe_update_proof_ns env1;
                                             (let uu____22294 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____22294
                                              then
                                                let uu____22295 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____22296 =
                                                  let uu____22297 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____22298 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____22297 uu____22298 in
                                                FStar_Errors.diag uu____22295
                                                  uu____22296
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
      let uu____22310 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22310 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22316 =
            let uu____22317 =
              let uu____22322 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____22322) in
            FStar_Errors.Error uu____22317 in
          raise uu____22316
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22331 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____22331 with
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
        let uu____22349 = FStar_Syntax_Unionfind.find u in
        match uu____22349 with
        | FStar_Pervasives_Native.None  -> true
        | uu____22352 -> false in
      let rec until_fixpoint acc implicits =
        let uu____22370 = acc in
        match uu____22370 with
        | (out,changed) ->
            (match implicits with
             | [] ->
                 if Prims.op_Negation changed
                 then out
                 else until_fixpoint ([], false) out
             | hd1::tl1 ->
                 let uu____22456 = hd1 in
                 (match uu____22456 with
                  | (uu____22469,env,u,tm,k,r) ->
                      let uu____22475 = unresolved u in
                      if uu____22475
                      then until_fixpoint ((hd1 :: out), changed) tl1
                      else
                        (let env1 =
                           FStar_TypeChecker_Env.set_expected_typ env k in
                         let tm1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta] env1 tm in
                         (let uu____22506 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "RelCheck") in
                          if uu____22506
                          then
                            let uu____22507 =
                              FStar_Syntax_Print.uvar_to_string u in
                            let uu____22508 =
                              FStar_Syntax_Print.term_to_string tm1 in
                            let uu____22509 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print3
                              "Checking uvar %s resolved to %s at type %s\n"
                              uu____22507 uu____22508 uu____22509
                          else ());
                         (let env2 =
                            if forcelax
                            then
                              let uu___186_22512 = env1 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___186_22512.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___186_22512.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___186_22512.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___186_22512.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___186_22512.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___186_22512.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___186_22512.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___186_22512.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___186_22512.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___186_22512.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___186_22512.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___186_22512.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___186_22512.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___186_22512.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___186_22512.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___186_22512.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___186_22512.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___186_22512.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___186_22512.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___186_22512.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___186_22512.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___186_22512.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___186_22512.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___186_22512.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___186_22512.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___186_22512.FStar_TypeChecker_Env.is_native_tactic)
                              }
                            else env1 in
                          let uu____22514 =
                            env2.FStar_TypeChecker_Env.type_of
                              (let uu___187_22522 = env2 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___187_22522.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___187_22522.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___187_22522.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___187_22522.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___187_22522.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___187_22522.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___187_22522.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___187_22522.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___187_22522.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___187_22522.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___187_22522.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___187_22522.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___187_22522.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___187_22522.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___187_22522.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___187_22522.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___187_22522.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___187_22522.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___187_22522.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___187_22522.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___187_22522.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___187_22522.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___187_22522.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___187_22522.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___187_22522.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___187_22522.FStar_TypeChecker_Env.is_native_tactic)
                               }) tm1 in
                          match uu____22514 with
                          | (uu____22523,uu____22524,g1) ->
                              let g2 =
                                if env2.FStar_TypeChecker_Env.is_pattern
                                then
                                  let uu___188_22527 = g1 in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      FStar_TypeChecker_Common.Trivial;
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___188_22527.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___188_22527.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits =
                                      (uu___188_22527.FStar_TypeChecker_Env.implicits)
                                  }
                                else g1 in
                              let g' =
                                let uu____22530 =
                                  discharge_guard'
                                    (FStar_Pervasives_Native.Some
                                       (fun uu____22536  ->
                                          FStar_Syntax_Print.term_to_string
                                            tm1)) env2 g2 true in
                                match uu____22530 with
                                | FStar_Pervasives_Native.Some g3 -> g3
                                | FStar_Pervasives_Native.None  ->
                                    failwith
                                      "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                              until_fixpoint
                                ((FStar_List.append
                                    g'.FStar_TypeChecker_Env.implicits out),
                                  true) tl1)))) in
      let uu___189_22564 = g in
      let uu____22565 =
        until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___189_22564.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___189_22564.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs =
          (uu___189_22564.FStar_TypeChecker_Env.univ_ineqs);
        FStar_TypeChecker_Env.implicits = uu____22565
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
        let uu____22623 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____22623 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____22636 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____22636
      | (reason,uu____22638,uu____22639,e,t,r)::uu____22643 ->
          let uu____22670 =
            let uu____22671 =
              let uu____22676 =
                let uu____22677 = FStar_Syntax_Print.term_to_string t in
                let uu____22678 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____22677 uu____22678 in
              (uu____22676, r) in
            FStar_Errors.Error uu____22671 in
          raise uu____22670
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___190_22687 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___190_22687.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___190_22687.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___190_22687.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22716 = try_teq false env t1 t2 in
        match uu____22716 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____22720 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____22720 with
             | FStar_Pervasives_Native.Some uu____22725 -> true
             | FStar_Pervasives_Native.None  -> false)