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
                let uu____150 =
                  let uu____151 =
                    let uu____170 =
                      let uu____173 = FStar_Syntax_Syntax.as_arg e in
                      [uu____173] in
                    (f, uu____170) in
                  FStar_Syntax_Syntax.Tm_app uu____151 in
                FStar_Syntax_Syntax.mk uu____150 in
              uu____145
                (FStar_Pervasives_Native.Some
                   (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
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
          let uu___137_194 = g in
          let uu____195 =
            let uu____196 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____196 in
          {
            FStar_TypeChecker_Env.guard_f = uu____195;
            FStar_TypeChecker_Env.deferred =
              (uu___137_194.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___137_194.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___137_194.FStar_TypeChecker_Env.implicits)
          }
let trivial: FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____201 -> failwith "impossible"
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
          let uu____214 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____214
let check_trivial:
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula =
  fun t  ->
    let uu____219 =
      let uu____220 = FStar_Syntax_Util.unmeta t in
      uu____220.FStar_Syntax_Syntax.n in
    match uu____219 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____226 -> FStar_TypeChecker_Common.NonTrivial t
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
        let uu____262 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
        {
          FStar_TypeChecker_Env.guard_f = uu____262;
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
                       let uu____336 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____336
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___138_338 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___138_338.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___138_338.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___138_338.FStar_TypeChecker_Env.implicits)
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
               let uu____360 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____360
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
            let uu___139_376 = g in
            let uu____377 =
              let uu____378 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____378 in
            {
              FStar_TypeChecker_Env.guard_f = uu____377;
              FStar_TypeChecker_Env.deferred =
                (uu___139_376.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___139_376.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___139_376.FStar_TypeChecker_Env.implicits)
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
                (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.n)) r in
            (uv1, uv1)
        | uu____417 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____444 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____444 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r in
            let uu____458 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.n)) r in
            (uu____458, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____501 = FStar_Syntax_Util.type_u () in
        match uu____501 with
        | (t_type,u) ->
            let uu____508 =
              let uu____513 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____513 t_type in
            (match uu____508 with
             | (tt,uu____515) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____549 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____591 -> false
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
    match projectee with | Success _0 -> true | uu____785 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____803 -> false
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
    match projectee with | COVARIANT  -> true | uu____828 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____833 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____838 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___107_862  ->
    match uu___107_862 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____878 =
    let uu____879 = FStar_Syntax_Subst.compress t in
    uu____879.FStar_Syntax_Syntax.n in
  match uu____878 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____918 = FStar_Syntax_Print.uvar_to_string u in
      let uu____919 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____918 uu____919
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____922;
         FStar_Syntax_Syntax.pos = uu____923;
         FStar_Syntax_Syntax.vars = uu____924;_},args)
      ->
      let uu____986 = FStar_Syntax_Print.uvar_to_string u in
      let uu____987 = FStar_Syntax_Print.term_to_string ty in
      let uu____988 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" uu____986 uu____987 uu____988
  | uu____989 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___108_997  ->
      match uu___108_997 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1003 =
            let uu____1006 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____1007 =
              let uu____1010 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____1011 =
                let uu____1014 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____1015 =
                  let uu____1018 =
                    let uu____1021 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____1022 =
                      let uu____1025 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____1026 =
                        let uu____1029 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (FStar_Pervasives_Native.fst
                               p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____1030 =
                          let uu____1033 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____1033] in
                        uu____1029 :: uu____1030 in
                      uu____1025 :: uu____1026 in
                    uu____1021 :: uu____1022 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____1018 in
                uu____1014 :: uu____1015 in
              uu____1010 :: uu____1011 in
            uu____1006 :: uu____1007 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____1003
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1041 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____1042 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____1041
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1042
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___109_1050  ->
      match uu___109_1050 with
      | UNIV (u,t) ->
          let x =
            let uu____1054 = FStar_Options.hide_uvar_nums () in
            if uu____1054
            then "?"
            else
              (let uu____1056 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____1056 FStar_Util.string_of_int) in
          let uu____1057 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____1057
      | TERM ((u,uu____1059),t) ->
          let x =
            let uu____1066 = FStar_Options.hide_uvar_nums () in
            if uu____1066
            then "?"
            else
              (let uu____1068 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____1068 FStar_Util.string_of_int) in
          let uu____1069 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____1069
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____1082 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____1082 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____1095 =
      let uu____1098 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____1098
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____1095 (FStar_String.concat ", ")
let args_to_string args =
  let uu____1128 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____1146  ->
            match uu____1146 with
            | (x,uu____1152) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right uu____1128 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____1159 =
      let uu____1160 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____1160 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1159;
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
        let uu___140_1179 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___140_1179.wl_deferred);
          ctr = (uu___140_1179.ctr);
          defer_ok = (uu___140_1179.defer_ok);
          smt_ok;
          tcenv = (uu___140_1179.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___141_1215 = empty_worklist env in
  let uu____1216 = FStar_List.map FStar_Pervasives_Native.snd g in
  {
    attempting = uu____1216;
    wl_deferred = (uu___141_1215.wl_deferred);
    ctr = (uu___141_1215.ctr);
    defer_ok = false;
    smt_ok = (uu___141_1215.smt_ok);
    tcenv = (uu___141_1215.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___142_1233 = wl in
        {
          attempting = (uu___142_1233.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___142_1233.ctr);
          defer_ok = (uu___142_1233.defer_ok);
          smt_ok = (uu___142_1233.smt_ok);
          tcenv = (uu___142_1233.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___143_1252 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___143_1252.wl_deferred);
        ctr = (uu___143_1252.ctr);
        defer_ok = (uu___143_1252.defer_ok);
        smt_ok = (uu___143_1252.smt_ok);
        tcenv = (uu___143_1252.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1266 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____1266
         then
           let uu____1267 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1267
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___110_1272  ->
    match uu___110_1272 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___144_1297 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___144_1297.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___144_1297.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___144_1297.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___144_1297.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___144_1297.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___144_1297.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___144_1297.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___111_1330  ->
    match uu___111_1330 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___112_1356  ->
      match uu___112_1356 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___113_1360  ->
    match uu___113_1360 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___114_1374  ->
    match uu___114_1374 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___115_1390  ->
    match uu___115_1390 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___116_1406  ->
    match uu___116_1406 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___117_1424  ->
    match uu___117_1424 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___118_1442  ->
    match uu___118_1442 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___119_1456  ->
    match uu___119_1456 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____1479 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1479 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1492  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1555 = next_pid () in
  let uu____1556 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1555;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1556;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1618 = next_pid () in
  let uu____1619 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1618;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1619;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1674 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1674;
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
let guard_on_element wl problem x phi =
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
        let uu____1752 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1752
        then
          let uu____1753 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1754 = prob_to_string env d in
          let uu____1755 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1753 uu____1754 uu____1755 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1761 -> failwith "impossible" in
           let uu____1762 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1776 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1777 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1776, uu____1777)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1783 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1784 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1783, uu____1784) in
           match uu____1762 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___120_1801  ->
            match uu___120_1801 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1813 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1815),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___121_1837  ->
           match uu___121_1837 with
           | UNIV uu____1840 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1846),t) ->
               let uu____1852 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1852
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
        (fun uu___122_1874  ->
           match uu___122_1874 with
           | UNIV (u',t) ->
               let uu____1879 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1879
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1883 -> FStar_Pervasives_Native.None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1892 =
        let uu____1893 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1893 in
      FStar_Syntax_Subst.compress uu____1892
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1902 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1902
let norm_arg env t =
  let uu____1930 = sn env (FStar_Pervasives_Native.fst t) in
  (uu____1930, (FStar_Pervasives_Native.snd t))
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
           (fun uu____1963  ->
              match uu____1963 with
              | (x,imp) ->
                  let uu____1974 =
                    let uu___145_1975 = x in
                    let uu____1976 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___145_1975.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___145_1975.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1976
                    } in
                  (uu____1974, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1995 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1995
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1999 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1999
        | uu____2002 -> u2 in
      let uu____2003 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2003
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then
          ((x.FStar_Syntax_Syntax.sort),
            (FStar_Pervasives_Native.Some (x, phi)))
        else
          (let uu____2176 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____2176 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____2197;
               FStar_Syntax_Syntax.pos = uu____2198;
               FStar_Syntax_Syntax.vars = uu____2199;_} ->
               ((x1.FStar_Syntax_Syntax.sort),
                 (FStar_Pervasives_Native.Some (x1, phi1)))
           | tt ->
               let uu____2239 =
                 let uu____2240 = FStar_Syntax_Print.term_to_string tt in
                 let uu____2241 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____2240
                   uu____2241 in
               failwith uu____2239)
    | FStar_Syntax_Syntax.Tm_uinst uu____2260 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____2311 =
             let uu____2312 = FStar_Syntax_Subst.compress t1' in
             uu____2312.FStar_Syntax_Syntax.n in
           match uu____2311 with
           | FStar_Syntax_Syntax.Tm_refine uu____2335 -> aux true t1'
           | uu____2344 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_fvar uu____2367 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____2410 =
             let uu____2411 = FStar_Syntax_Subst.compress t1' in
             uu____2411.FStar_Syntax_Syntax.n in
           match uu____2410 with
           | FStar_Syntax_Syntax.Tm_refine uu____2434 -> aux true t1'
           | uu____2443 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_app uu____2466 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____2527 =
             let uu____2528 = FStar_Syntax_Subst.compress t1' in
             uu____2528.FStar_Syntax_Syntax.n in
           match uu____2527 with
           | FStar_Syntax_Syntax.Tm_refine uu____2551 -> aux true t1'
           | uu____2560 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_type uu____2583 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_constant uu____2606 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_name uu____2629 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_bvar uu____2652 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_arrow uu____2675 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_abs uu____2712 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_uvar uu____2753 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_let uu____2796 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_match uu____2833 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_meta uu____2884 ->
        let uu____2893 =
          let uu____2894 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2895 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2894
            uu____2895 in
        failwith uu____2893
    | FStar_Syntax_Syntax.Tm_ascribed uu____2914 ->
        let uu____2949 =
          let uu____2950 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2951 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2950
            uu____2951 in
        failwith uu____2949
    | FStar_Syntax_Syntax.Tm_delayed uu____2970 ->
        let uu____2999 =
          let uu____3000 = FStar_Syntax_Print.term_to_string t11 in
          let uu____3001 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3000
            uu____3001 in
        failwith uu____2999
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____3020 =
          let uu____3021 = FStar_Syntax_Print.term_to_string t11 in
          let uu____3022 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3021
            uu____3022 in
        failwith uu____3020 in
  let uu____3041 = whnf env t1 in aux false uu____3041
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____3054 =
        let uu____3073 = empty_worklist env in
        base_and_refinement env uu____3073 t in
      FStar_All.pipe_right uu____3054 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____3118 = FStar_Syntax_Syntax.null_bv t in
    (uu____3118, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____3144 = base_and_refinement env wl t in
  match uu____3144 with
  | (t_base,refinement) ->
      (match refinement with
       | FStar_Pervasives_Native.None  -> trivial_refinement t_base
       | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
let force_refinement uu____3253 =
  match uu____3253 with
  | (t_base,refopt) ->
      let uu____3278 =
        match refopt with
        | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
        | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
      (match uu____3278 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___123_3310  ->
      match uu___123_3310 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____3316 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____3317 =
            let uu____3318 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____3318 in
          let uu____3319 =
            let uu____3320 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____3320 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____3316 uu____3317
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____3319
      | FStar_TypeChecker_Common.CProb p ->
          let uu____3326 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____3327 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____3328 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____3326 uu____3327
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____3328
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____3333 =
      let uu____3336 =
        let uu____3339 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3362  ->
                  match uu____3362 with | (uu____3369,uu____3370,x) -> x)) in
        FStar_List.append wl.attempting uu____3339 in
      FStar_List.map (wl_prob_to_string wl) uu____3336 in
    FStar_All.pipe_right uu____3333 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3398 =
          let uu____3417 =
            let uu____3418 = FStar_Syntax_Subst.compress k in
            uu____3418.FStar_Syntax_Syntax.n in
          match uu____3417 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3489 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____3489)
              else
                (let uu____3515 = FStar_Syntax_Util.abs_formals t in
                 match uu____3515 with
                 | (ys',t1,uu____3544) ->
                     let uu____3549 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3549))
          | uu____3590 ->
              let uu____3591 =
                let uu____3602 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3602) in
              ((ys, t), uu____3591) in
        match uu____3398 with
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
                 let uu____3683 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3683 c in
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
            let uu____3716 = p_guard prob in
            match uu____3716 with
            | (uu____3721,uv) ->
                ((let uu____3724 =
                    let uu____3725 = FStar_Syntax_Subst.compress uv in
                    uu____3725.FStar_Syntax_Syntax.n in
                  match uu____3724 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3767 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3767
                        then
                          let uu____3768 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3769 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3770 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3768
                            uu____3769 uu____3770
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3772 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___146_3775 = wl in
                  {
                    attempting = (uu___146_3775.attempting);
                    wl_deferred = (uu___146_3775.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___146_3775.defer_ok);
                    smt_ok = (uu___146_3775.smt_ok);
                    tcenv = (uu___146_3775.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3793 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3793
         then
           let uu____3794 = FStar_Util.string_of_int pid in
           let uu____3795 =
             let uu____3796 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3796 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3794 uu____3795
         else ());
        commit sol;
        (let uu___147_3803 = wl in
         {
           attempting = (uu___147_3803.attempting);
           wl_deferred = (uu___147_3803.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___147_3803.defer_ok);
           smt_ok = (uu___147_3803.smt_ok);
           tcenv = (uu___147_3803.tcenv)
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
            | (uu____3845,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3857 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3857 in
          (let uu____3867 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3867
           then
             let uu____3868 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3869 =
               let uu____3870 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3870 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3868 uu____3869
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____3905 =
    let uu____3912 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____3912 FStar_Util.set_elements in
  FStar_All.pipe_right uu____3905
    (FStar_Util.for_some
       (fun uu____3948  ->
          match uu____3948 with
          | (uv,uu____3954) ->
              FStar_Syntax_Unionfind.equiv uv
                (FStar_Pervasives_Native.fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____4000 = occurs wl uk t in Prims.op_Negation uu____4000 in
  let msg =
    if occurs_ok
    then FStar_Pervasives_Native.None
    else
      (let uu____4007 =
         let uu____4008 =
           FStar_Syntax_Print.uvar_to_string (FStar_Pervasives_Native.fst uk) in
         let uu____4009 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____4008 uu____4009 in
       FStar_Pervasives_Native.Some uu____4007) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____4081 = occurs_check env wl uk t in
  match uu____4081 with
  | (occurs_ok,msg) ->
      let uu____4112 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____4112, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  ->
            fun x  -> FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____4224 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____4278  ->
            fun uu____4279  ->
              match (uu____4278, uu____4279) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____4360 =
                    let uu____4361 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____4361 in
                  if uu____4360
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____4386 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____4386
                     then
                       let uu____4399 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____4399)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____4224 with | (isect,uu____4440) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____4525  ->
          fun uu____4526  ->
            match (uu____4525, uu____4526) with
            | ((a,uu____4544),(b,uu____4546)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____4617 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____4631  ->
                match uu____4631 with
                | (b,uu____4637) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____4617
      then FStar_Pervasives_Native.None
      else
        FStar_Pervasives_Native.Some (a, (FStar_Pervasives_Native.snd hd1))
  | uu____4653 -> FStar_Pervasives_Native.None
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
            let uu____4728 = pat_var_opt env seen hd1 in
            (match uu____4728 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4742 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4742
                   then
                     let uu____4743 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4743
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4762 =
      let uu____4763 = FStar_Syntax_Subst.compress t in
      uu____4763.FStar_Syntax_Syntax.n in
    match uu____4762 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4768 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4789;
           FStar_Syntax_Syntax.tk = uu____4790;
           FStar_Syntax_Syntax.pos = uu____4791;
           FStar_Syntax_Syntax.vars = uu____4792;_},uu____4793)
        -> true
    | uu____4842 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____4972;
         FStar_Syntax_Syntax.pos = uu____4973;
         FStar_Syntax_Syntax.vars = uu____4974;_},args)
      -> (t, uv, k, args)
  | uu____5066 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____5172 = destruct_flex_t t in
  match uu____5172 with
  | (t1,uv,k,args) ->
      let uu____5319 = pat_vars env [] args in
      (match uu____5319 with
       | FStar_Pervasives_Native.Some vars ->
           ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
       | uu____5441 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5539 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5576 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5581 -> false
let head_match: match_result -> match_result =
  fun uu___124_5585  ->
    match uu___124_5585 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5600 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5611 ->
          let uu____5612 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____5612 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5623 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5644 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5655 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5686 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5687 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5688 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5709 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5724 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5754) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5764,uu____5765) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5823) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5852;
             FStar_Syntax_Syntax.index = uu____5853;
             FStar_Syntax_Syntax.sort = t2;_},uu____5855)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5868 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5869 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5870 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5885 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5905 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5905
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
            let uu____5929 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5929
            then FullMatch
            else
              (let uu____5931 =
                 let uu____5940 =
                   let uu____5943 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5943 in
                 let uu____5944 =
                   let uu____5947 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5947 in
                 (uu____5940, uu____5944) in
               MisMatch uu____5931)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5953),FStar_Syntax_Syntax.Tm_uinst (g,uu____5955)) ->
            let uu____5972 = head_matches env f g in
            FStar_All.pipe_right uu____5972 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5981),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5983)) ->
            let uu____6048 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____6048
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6055),FStar_Syntax_Syntax.Tm_refine (y,uu____6057)) ->
            let uu____6074 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____6074 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6076),uu____6077) ->
            let uu____6086 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____6086 head_match
        | (uu____6087,FStar_Syntax_Syntax.Tm_refine (x,uu____6089)) ->
            let uu____6098 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____6098 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6099,FStar_Syntax_Syntax.Tm_type
           uu____6100) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6101,FStar_Syntax_Syntax.Tm_arrow uu____6102) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6132),FStar_Syntax_Syntax.Tm_app (head',uu____6134))
            ->
            let uu____6191 = head_matches env head1 head' in
            FStar_All.pipe_right uu____6191 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6193),uu____6194) ->
            let uu____6223 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____6223 head_match
        | (uu____6224,FStar_Syntax_Syntax.Tm_app (head1,uu____6226)) ->
            let uu____6255 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____6255 head_match
        | uu____6256 ->
            let uu____6261 =
              let uu____6270 = delta_depth_of_term env t11 in
              let uu____6273 = delta_depth_of_term env t21 in
              (uu____6270, uu____6273) in
            MisMatch uu____6261
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____6323 = FStar_Syntax_Util.head_and_args t in
    match uu____6323 with
    | (head1,uu____6345) ->
        let uu____6374 =
          let uu____6375 = FStar_Syntax_Util.un_uinst head1 in
          uu____6375.FStar_Syntax_Syntax.n in
        (match uu____6374 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____6383 =
               let uu____6384 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____6384 FStar_Option.isSome in
             if uu____6383
             then
               let uu____6403 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____6403
                 (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
             else FStar_Pervasives_Native.None
         | uu____6407 -> FStar_Pervasives_Native.None) in
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
        (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational
         ),uu____6510)
        ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____6528 =
             let uu____6537 = maybe_inline t11 in
             let uu____6540 = maybe_inline t21 in (uu____6537, uu____6540) in
           match uu____6528 with
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
               fail r
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.None )
               -> aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t22)
               -> aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.Some
              t22) -> aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch
        (uu____6577,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Delta_equational ))
        ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____6595 =
             let uu____6604 = maybe_inline t11 in
             let uu____6607 = maybe_inline t21 in (uu____6604, uu____6607) in
           match uu____6595 with
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
               fail r
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.None )
               -> aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t22)
               -> aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.Some
              t22) -> aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch
        (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some d2)
        when d1 = d2 ->
        let uu____6650 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____6650 with
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
        (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some d2) ->
        let d1_greater_than_d2 =
          FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
        let uu____6673 =
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
        (match uu____6673 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____6697 -> fail r
    | uu____6706 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____6740 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____6778 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6797 = FStar_Syntax_Util.type_u () in
      match uu____6797 with
      | (t,uu____6803) ->
          let uu____6804 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____6804
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6817 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____6817 FStar_Pervasives_Native.fst
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
        let uu____6883 = head_matches env t1 t' in
        match uu____6883 with
        | MisMatch uu____6884 -> false
        | uu____6893 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____7005,imp),T (t2,uu____7008)) -> (t2, imp)
                     | uu____7033 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____7106  ->
                    match uu____7106 with
                    | (t2,uu____7120) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____7169 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____7169 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____7250))::tcs2) ->
                       aux
                         (((let uu___148_7285 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_7285.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_7285.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____7303 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___125_7358 =
                 match uu___125_7358 with
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
               let uu____7477 = decompose1 [] bs1 in
               (rebuild, matches, uu____7477))
      | uu____7528 ->
          let rebuild uu___126_7534 =
            match uu___126_7534 with
            | [] -> t1
            | uu____7537 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___127_7569  ->
    match uu___127_7569 with
    | T (t,uu____7571) -> t
    | uu____7580 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___128_7584  ->
    match uu___128_7584 with
    | T (t,uu____7586) -> FStar_Syntax_Syntax.as_arg t
    | uu____7595 -> failwith "Impossible"
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
              | (uu____7710,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____7735 = new_uvar r scope1 k in
                  (match uu____7735 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7755 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____7776 =
                         let uu____7777 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____7777 in
                       ((T (gi_xs, mk_kind)), uu____7776))
              | (uu____7790,uu____7791,C uu____7792) -> failwith "impos" in
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
                         FStar_Syntax_Syntax.tk = uu____7960;
                         FStar_Syntax_Syntax.pos = uu____7961;
                         FStar_Syntax_Syntax.vars = uu____7962;_})
                        ->
                        let uu____7991 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7991 with
                         | (T (gi_xs,uu____8017),prob) ->
                             let uu____8027 =
                               let uu____8028 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____8028 in
                             (uu____8027, [prob])
                         | uu____8031 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____8046;
                         FStar_Syntax_Syntax.pos = uu____8047;
                         FStar_Syntax_Syntax.vars = uu____8048;_})
                        ->
                        let uu____8077 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____8077 with
                         | (T (gi_xs,uu____8103),prob) ->
                             let uu____8113 =
                               let uu____8114 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____8114 in
                             (uu____8113, [prob])
                         | uu____8117 -> failwith "impossible")
                    | (uu____8128,uu____8129,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____8131;
                         FStar_Syntax_Syntax.pos = uu____8132;
                         FStar_Syntax_Syntax.vars = uu____8133;_})
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
                        let uu____8270 =
                          let uu____8279 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____8279 FStar_List.unzip in
                        (match uu____8270 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____8333 =
                                 let uu____8334 =
                                   let uu____8339 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____8339 un_T in
                                 let uu____8340 =
                                   let uu____8351 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____8351
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____8334;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____8340;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____8333 in
                             ((C gi_xs), sub_probs))
                    | uu____8360 ->
                        let uu____8373 = sub_prob scope1 args q in
                        (match uu____8373 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____7943 with
                   | (tc,probs) ->
                       let uu____8404 =
                         match q with
                         | (FStar_Pervasives_Native.Some
                            b,uu____8454,uu____8455) ->
                             let uu____8470 =
                               let uu____8477 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____8477 :: args in
                             ((FStar_Pervasives_Native.Some b), (b ::
                               scope1), uu____8470)
                         | uu____8512 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____8404 with
                        | (bopt,scope2,args1) ->
                            let uu____8594 = aux scope2 args1 qs2 in
                            (match uu____8594 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____8631 =
                                         let uu____8634 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____8634 in
                                       FStar_Syntax_Util.mk_conj_l uu____8631
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____8657 =
                                         let uu____8660 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____8661 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____8660 :: uu____8661 in
                                       FStar_Syntax_Util.mk_conj_l uu____8657 in
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
let compress_tprob wl p =
  let uu___149_8753 = p in
  let uu____8758 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____8759 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___149_8753.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____8758;
    FStar_TypeChecker_Common.relation =
      (uu___149_8753.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____8759;
    FStar_TypeChecker_Common.element =
      (uu___149_8753.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___149_8753.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___149_8753.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___149_8753.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___149_8753.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___149_8753.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8773 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____8773
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____8782 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8804 = compress_prob wl pr in
        FStar_All.pipe_right uu____8804 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8814 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8814 with
           | (lh,uu____8838) ->
               let uu____8867 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8867 with
                | (rh,uu____8891) ->
                    let uu____8920 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8937,FStar_Syntax_Syntax.Tm_uvar uu____8938)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8983,uu____8984)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____9009,FStar_Syntax_Syntax.Tm_uvar uu____9010)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9035,uu____9036)
                          ->
                          let uu____9057 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____9057 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____9134 ->
                                    let rank =
                                      let uu____9146 = is_top_level_prob prob in
                                      if uu____9146
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____9148 =
                                      let uu___150_9153 = tp in
                                      let uu____9158 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___150_9153.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___150_9153.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___150_9153.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____9158;
                                        FStar_TypeChecker_Common.element =
                                          (uu___150_9153.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___150_9153.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___150_9153.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___150_9153.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___150_9153.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___150_9153.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____9148)))
                      | (uu____9177,FStar_Syntax_Syntax.Tm_uvar uu____9178)
                          ->
                          let uu____9199 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____9199 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____9276 ->
                                    let uu____9287 =
                                      let uu___151_9296 = tp in
                                      let uu____9301 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___151_9296.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____9301;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___151_9296.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___151_9296.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___151_9296.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___151_9296.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___151_9296.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___151_9296.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___151_9296.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___151_9296.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____9287)))
                      | (uu____9332,uu____9333) -> (rigid_rigid, tp) in
                    (match uu____8920 with
                     | (rank,tp1) ->
                         let uu____9352 =
                           FStar_All.pipe_right
                             (let uu___152_9358 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___152_9358.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___152_9358.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___152_9358.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___152_9358.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___152_9358.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___152_9358.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___152_9358.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___152_9358.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___152_9358.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50) in
                         (rank, uu____9352))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9368 =
            FStar_All.pipe_right
              (let uu___153_9374 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___153_9374.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___153_9374.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___153_9374.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___153_9374.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___153_9374.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___153_9374.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___153_9374.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___153_9374.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___153_9374.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51) in
          (rigid_rigid, uu____9368)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____9430 probs =
      match uu____9430 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____9483 = rank wl hd1 in
               (match uu____9483 with
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
    match projectee with | UDeferred _0 -> true | uu____9593 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9607 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9621 -> false
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
                        let uu____9666 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____9666 with
                        | (k,uu____9672) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9682 -> false)))
            | uu____9683 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____9734 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____9734 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____9737 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____9747 =
                     let uu____9748 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____9749 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____9748
                       uu____9749 in
                   UFailed uu____9747)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9769 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____9769 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9791 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____9791 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____9794 ->
                let uu____9799 =
                  let uu____9800 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____9801 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9800
                    uu____9801 msg in
                UFailed uu____9799 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9802,uu____9803) ->
              let uu____9804 =
                let uu____9805 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9806 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9805 uu____9806 in
              failwith uu____9804
          | (FStar_Syntax_Syntax.U_unknown ,uu____9807) ->
              let uu____9808 =
                let uu____9809 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9810 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9809 uu____9810 in
              failwith uu____9808
          | (uu____9811,FStar_Syntax_Syntax.U_bvar uu____9812) ->
              let uu____9813 =
                let uu____9814 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9815 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9814 uu____9815 in
              failwith uu____9813
          | (uu____9816,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9817 =
                let uu____9818 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9819 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9818 uu____9819 in
              failwith uu____9817
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9843 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____9843
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____9865 = occurs_univ v1 u3 in
              if uu____9865
              then
                let uu____9866 =
                  let uu____9867 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9868 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9867 uu____9868 in
                try_umax_components u11 u21 uu____9866
              else
                (let uu____9870 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9870)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9890 = occurs_univ v1 u3 in
              if uu____9890
              then
                let uu____9891 =
                  let uu____9892 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9893 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9892 uu____9893 in
                try_umax_components u11 u21 uu____9891
              else
                (let uu____9895 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9895)
          | (FStar_Syntax_Syntax.U_max uu____9904,uu____9905) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9911 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9911
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9913,FStar_Syntax_Syntax.U_max uu____9914) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9920 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9920
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9922,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9923,FStar_Syntax_Syntax.U_name
             uu____9924) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9925) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9926) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9927,FStar_Syntax_Syntax.U_succ
             uu____9928) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9929,FStar_Syntax_Syntax.U_zero
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
let match_num_binders bc1 bc2 =
  let uu____10023 = bc1 in
  match uu____10023 with
  | (bs1,mk_cod1) ->
      let uu____10064 = bc2 in
      (match uu____10064 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____10134 = FStar_Util.first_N n1 bs in
             match uu____10134 with
             | (bs3,rest) ->
                 let uu____10159 = mk_cod rest in (bs3, uu____10159) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____10188 =
               let uu____10195 = mk_cod1 [] in (bs1, uu____10195) in
             let uu____10198 =
               let uu____10205 = mk_cod2 [] in (bs2, uu____10205) in
             (uu____10188, uu____10198)
           else
             if l1 > l2
             then
               (let uu____10247 = curry l2 bs1 mk_cod1 in
                let uu____10260 =
                  let uu____10267 = mk_cod2 [] in (bs2, uu____10267) in
                (uu____10247, uu____10260))
             else
               (let uu____10283 =
                  let uu____10290 = mk_cod1 [] in (bs1, uu____10290) in
                let uu____10293 = curry l1 bs2 mk_cod2 in
                (uu____10283, uu____10293)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____10414 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____10414
       then
         let uu____10415 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10415
       else ());
      (let uu____10417 = next_prob probs in
       match uu____10417 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___154_10438 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___154_10438.wl_deferred);
               ctr = (uu___154_10438.ctr);
               defer_ok = (uu___154_10438.defer_ok);
               smt_ok = (uu___154_10438.smt_ok);
               tcenv = (uu___154_10438.tcenv)
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
                  let uu____10449 = solve_flex_rigid_join env tp probs1 in
                  (match uu____10449 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____10454 = solve_rigid_flex_meet env tp probs1 in
                     match uu____10454 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____10459,uu____10460) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____10477 ->
                let uu____10486 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10545  ->
                          match uu____10545 with
                          | (c,uu____10553,uu____10554) -> c < probs.ctr)) in
                (match uu____10486 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10595 =
                            FStar_List.map
                              (fun uu____10610  ->
                                 match uu____10610 with
                                 | (uu____10621,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____10595
                      | uu____10624 ->
                          let uu____10633 =
                            let uu___155_10634 = probs in
                            let uu____10635 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10656  ->
                                      match uu____10656 with
                                      | (uu____10663,uu____10664,y) -> y)) in
                            {
                              attempting = uu____10635;
                              wl_deferred = rest;
                              ctr = (uu___155_10634.ctr);
                              defer_ok = (uu___155_10634.defer_ok);
                              smt_ok = (uu___155_10634.smt_ok);
                              tcenv = (uu___155_10634.tcenv)
                            } in
                          solve env uu____10633))))
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
            let uu____10671 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____10671 with
            | USolved wl1 ->
                let uu____10673 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____10673
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
                  let uu____10719 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____10719 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10722 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____10734;
                  FStar_Syntax_Syntax.pos = uu____10735;
                  FStar_Syntax_Syntax.vars = uu____10736;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____10739;
                  FStar_Syntax_Syntax.pos = uu____10740;
                  FStar_Syntax_Syntax.vars = uu____10741;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10763,uu____10764) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10773,FStar_Syntax_Syntax.Tm_uinst uu____10774) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10783 -> USolved wl
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
            ((let uu____10793 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____10793
              then
                let uu____10794 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10794 msg
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
        (let uu____10803 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10803
         then
           let uu____10804 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____10804
         else ());
        (let uu____10806 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____10806 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10880 = head_matches_delta env () t1 t2 in
               match uu____10880 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10921 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10970 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10985 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____10986 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____10985, uu____10986)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10991 =
                                FStar_Syntax_Subst.compress t1 in
                              let uu____10992 =
                                FStar_Syntax_Subst.compress t2 in
                              (uu____10991, uu____10992) in
                        (match uu____10970 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____11026 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____11026 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____11067 =
                                    let uu____11078 =
                                      let uu____11083 =
                                        let uu____11088 =
                                          let uu____11089 =
                                            let uu____11098 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____11098) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____11089 in
                                        FStar_Syntax_Syntax.mk uu____11088 in
                                      uu____11083
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____11111 =
                                      let uu____11114 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____11114] in
                                    (uu____11078, uu____11111) in
                                  FStar_Pervasives_Native.Some uu____11067
                              | (uu____11131,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____11133)) ->
                                  let uu____11142 =
                                    let uu____11149 =
                                      let uu____11152 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____11152] in
                                    (t11, uu____11149) in
                                  FStar_Pervasives_Native.Some uu____11142
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____11162),uu____11163) ->
                                  let uu____11172 =
                                    let uu____11179 =
                                      let uu____11182 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____11182] in
                                    (t21, uu____11179) in
                                  FStar_Pervasives_Native.Some uu____11172
                              | uu____11191 ->
                                  let uu____11196 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____11196 with
                                   | (head1,uu____11224) ->
                                       let uu____11253 =
                                         let uu____11254 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____11254.FStar_Syntax_Syntax.n in
                                       (match uu____11253 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____11267;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____11269;_}
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
                                        | uu____11276 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11291) ->
                  let uu____11324 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___129_11350  ->
                            match uu___129_11350 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____11357 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____11357 with
                                      | (u',uu____11377) ->
                                          let uu____11406 =
                                            let uu____11407 = whnf env u' in
                                            uu____11407.FStar_Syntax_Syntax.n in
                                          (match uu____11406 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____11413) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____11446 -> false))
                                 | uu____11447 -> false)
                            | uu____11450 -> false)) in
                  (match uu____11324 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____11484 tps =
                         match uu____11484 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____11532 =
                                    let uu____11541 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____11541 in
                                  (match uu____11532 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____11576 -> FStar_Pervasives_Native.None) in
                       let uu____11585 =
                         let uu____11594 =
                           let uu____11601 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____11601, []) in
                         make_lower_bound uu____11594 lower_bounds in
                       (match uu____11585 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____11613 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____11613
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
                            ((let uu____11633 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____11633
                              then
                                let wl' =
                                  let uu___156_11635 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___156_11635.wl_deferred);
                                    ctr = (uu___156_11635.ctr);
                                    defer_ok = (uu___156_11635.defer_ok);
                                    smt_ok = (uu___156_11635.smt_ok);
                                    tcenv = (uu___156_11635.tcenv)
                                  } in
                                let uu____11636 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____11636
                              else ());
                             (let uu____11638 =
                                solve_t env eq_prob
                                  (let uu___157_11640 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___157_11640.wl_deferred);
                                     ctr = (uu___157_11640.ctr);
                                     defer_ok = (uu___157_11640.defer_ok);
                                     smt_ok = (uu___157_11640.smt_ok);
                                     tcenv = (uu___157_11640.tcenv)
                                   }) in
                              match uu____11638 with
                              | Success uu____11643 ->
                                  let wl1 =
                                    let uu___158_11645 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___158_11645.wl_deferred);
                                      ctr = (uu___158_11645.ctr);
                                      defer_ok = (uu___158_11645.defer_ok);
                                      smt_ok = (uu___158_11645.smt_ok);
                                      tcenv = (uu___158_11645.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____11647 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____11652 -> FStar_Pervasives_Native.None))))
              | uu____11653 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____11662 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____11662
         then
           let uu____11663 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____11663
         else ());
        (let uu____11665 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____11665 with
         | (u,args) ->
             let uu____11716 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____11716 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____11757 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____11757 with
                    | (h1,args1) ->
                        let uu____11810 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____11810 with
                         | (h2,uu____11834) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____11869 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____11869
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____11889 =
                                          let uu____11892 =
                                            let uu____11893 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____11893 in
                                          [uu____11892] in
                                        FStar_Pervasives_Native.Some
                                          uu____11889))
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
                                       (let uu____11928 =
                                          let uu____11931 =
                                            let uu____11932 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____11932 in
                                          [uu____11931] in
                                        FStar_Pervasives_Native.Some
                                          uu____11928))
                                  else FStar_Pervasives_Native.None
                              | uu____11946 -> FStar_Pervasives_Native.None)) in
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
                             let uu____12060 =
                               let uu____12071 =
                                 let uu____12076 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____12076 in
                               (uu____12071, m1) in
                             FStar_Pervasives_Native.Some uu____12060)
                    | (uu____12093,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____12095)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____12155),uu____12156) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____12215 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____12278) ->
                       let uu____12311 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___130_12337  ->
                                 match uu___130_12337 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____12344 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____12344 with
                                           | (u',uu____12364) ->
                                               let uu____12393 =
                                                 let uu____12394 =
                                                   whnf env u' in
                                                 uu____12394.FStar_Syntax_Syntax.n in
                                               (match uu____12393 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____12400) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____12433 -> false))
                                      | uu____12434 -> false)
                                 | uu____12437 -> false)) in
                       (match uu____12311 with
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
                                       let uu____12555 =
                                         let uu____12568 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____12568 in
                                       (match uu____12555 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____12635 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____12648 =
                              let uu____12661 =
                                let uu____12672 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____12672, []) in
                              make_upper_bound uu____12661 upper_bounds in
                            (match uu____12648 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____12688 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____12688
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
                                 ((let uu____12720 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____12720
                                   then
                                     let wl' =
                                       let uu___159_12722 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___159_12722.wl_deferred);
                                         ctr = (uu___159_12722.ctr);
                                         defer_ok = (uu___159_12722.defer_ok);
                                         smt_ok = (uu___159_12722.smt_ok);
                                         tcenv = (uu___159_12722.tcenv)
                                       } in
                                     let uu____12723 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____12723
                                   else ());
                                  (let uu____12725 =
                                     solve_t env eq_prob
                                       (let uu___160_12727 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___160_12727.wl_deferred);
                                          ctr = (uu___160_12727.ctr);
                                          defer_ok =
                                            (uu___160_12727.defer_ok);
                                          smt_ok = (uu___160_12727.smt_ok);
                                          tcenv = (uu___160_12727.tcenv)
                                        }) in
                                   match uu____12725 with
                                   | Success uu____12730 ->
                                       let wl1 =
                                         let uu___161_12732 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___161_12732.wl_deferred);
                                           ctr = (uu___161_12732.ctr);
                                           defer_ok =
                                             (uu___161_12732.defer_ok);
                                           smt_ok = (uu___161_12732.smt_ok);
                                           tcenv = (uu___161_12732.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____12734 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____12739 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____12740 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____12831 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____12831
                      then
                        let uu____12832 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____12832
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___162_12886 = hd1 in
                      let uu____12887 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___162_12886.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___162_12886.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____12887
                      } in
                    let hd21 =
                      let uu___163_12893 = hd2 in
                      let uu____12894 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___163_12893.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___163_12893.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____12894
                      } in
                    let prob =
                      let uu____12900 =
                        let uu____12905 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____12905 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____12900 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____12918 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____12918 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____12922 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____12922 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____12954 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____12959 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____12954 uu____12959 in
                         ((let uu____12969 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____12969
                           then
                             let uu____12970 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____12971 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____12970 uu____12971
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____12998 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____13008 = aux scope env [] bs1 bs2 in
              match uu____13008 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____13032 = compress_tprob wl problem in
        solve_t' env uu____13032 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____13065 = head_matches_delta env1 wl1 t1 t2 in
          match uu____13065 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____13096,uu____13097) ->
                   let may_relate head3 =
                     let uu____13122 =
                       let uu____13123 = FStar_Syntax_Util.un_uinst head3 in
                       uu____13123.FStar_Syntax_Syntax.n in
                     match uu____13122 with
                     | FStar_Syntax_Syntax.Tm_name uu____13128 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____13129 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____13159 -> false in
                   let uu____13160 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____13160
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
                                let uu____13181 =
                                  let uu____13182 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____13182 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____13181 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____13184 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____13184
                   else
                     (let uu____13186 =
                        let uu____13187 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____13188 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____13187 uu____13188 in
                      giveup env1 uu____13186 orig)
               | (uu____13189,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___164_13203 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___164_13203.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___164_13203.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___164_13203.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___164_13203.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___164_13203.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___164_13203.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___164_13203.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___164_13203.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____13204,FStar_Pervasives_Native.None ) ->
                   ((let uu____13216 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13216
                     then
                       let uu____13217 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____13218 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____13219 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____13220 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____13217
                         uu____13218 uu____13219 uu____13220
                     else ());
                    (let uu____13222 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____13222 with
                     | (head11,args1) ->
                         let uu____13271 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____13271 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____13341 =
                                  let uu____13342 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____13343 = args_to_string args1 in
                                  let uu____13344 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____13345 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____13342 uu____13343 uu____13344
                                    uu____13345 in
                                giveup env1 uu____13341 orig
                              else
                                (let uu____13347 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____13353 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____13353 = FStar_Syntax_Util.Equal) in
                                 if uu____13347
                                 then
                                   let uu____13354 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____13354 with
                                   | USolved wl2 ->
                                       let uu____13356 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____13356
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____13360 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____13360 with
                                    | (base1,refinement1) ->
                                        let uu____13409 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____13409 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____13514 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____13514 with
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
                                                           (fun uu____13536 
                                                              ->
                                                              fun uu____13537
                                                                 ->
                                                                match 
                                                                  (uu____13536,
                                                                    uu____13537)
                                                                with
                                                                | ((a,uu____13555),
                                                                   (a',uu____13557))
                                                                    ->
                                                                    let uu____13566
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
                                                                    uu____13566)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____13576 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____13576 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____13582 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___165_13646 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___165_13646.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___165_13646.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___165_13646.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___165_13646.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___165_13646.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___165_13646.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___165_13646.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___165_13646.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____13668 = p in
          match uu____13668 with
          | (((u,k),xs,c),ps,(h,uu____13679,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13761 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____13761 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13784 = h gs_xs in
                     let uu____13785 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57) in
                     FStar_Syntax_Util.abs xs1 uu____13784 uu____13785 in
                   ((let uu____13791 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13791
                     then
                       let uu____13792 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____13793 = FStar_Syntax_Print.comp_to_string c in
                       let uu____13794 = FStar_Syntax_Print.term_to_string im in
                       let uu____13795 = FStar_Syntax_Print.tag_of_term im in
                       let uu____13796 =
                         let uu____13797 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____13797
                           (FStar_String.concat ", ") in
                       let uu____13802 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13792 uu____13793 uu____13794 uu____13795
                         uu____13796 uu____13802
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___131_13823 =
          match uu___131_13823 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____13855 = p in
          match uu____13855 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13946 = FStar_List.nth ps i in
              (match uu____13946 with
               | (pi,uu____13950) ->
                   let uu____13959 = FStar_List.nth xs i in
                   (match uu____13959 with
                    | (xi,uu____13971) ->
                        let rec gs k =
                          let uu____13984 = FStar_Syntax_Util.arrow_formals k in
                          match uu____13984 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____14077)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____14090 = new_uvar r xs k_a in
                                    (match uu____14090 with
                                     | (gi_xs,gi) ->
                                         let gi_xs1 =
                                           FStar_TypeChecker_Normalize.eta_expand
                                             env1 gi_xs in
                                         let gi_ps =
                                           FStar_Syntax_Syntax.mk_Tm_app gi
                                             ps
                                             (FStar_Pervasives_Native.Some
                                                (k_a.FStar_Syntax_Syntax.n))
                                             r in
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT
                                              (a, gi_xs1))
                                           :: subst1 in
                                         let uu____14114 = aux subst2 tl1 in
                                         (match uu____14114 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____14141 =
                                                let uu____14144 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____14144 :: gi_xs' in
                                              let uu____14145 =
                                                let uu____14148 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____14148 :: gi_ps' in
                                              (uu____14141, uu____14145))) in
                              aux [] bs in
                        let uu____14153 =
                          let uu____14154 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____14154 in
                        if uu____14153
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____14158 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____14158 with
                           | (g_xs,uu____14170) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____14181 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____14182 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58) in
                                 FStar_Syntax_Util.abs xs uu____14181
                                   uu____14182 in
                               let sub1 =
                                 let uu____14188 =
                                   let uu____14193 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____14198 =
                                     let uu____14203 =
                                       FStar_List.map
                                         (fun uu____14218  ->
                                            match uu____14218 with
                                            | (uu____14227,uu____14228,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____14203 in
                                   mk_problem (p_scope orig) orig uu____14193
                                     (p_rel orig) uu____14198
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____14188 in
                               ((let uu____14245 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____14245
                                 then
                                   let uu____14246 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____14247 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____14246 uu____14247
                                 else ());
                                (let wl2 =
                                   let uu____14250 =
                                     let uu____14253 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____14253 in
                                   solve_prob orig uu____14250
                                     [TERM (u, proj)] wl1 in
                                 let uu____14262 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____14262))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____14293 = lhs in
          match uu____14293 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____14329 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____14329 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____14362 =
                        let uu____14409 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____14409) in
                      FStar_Pervasives_Native.Some uu____14362
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____14553 =
                           let uu____14560 =
                             let uu____14561 = FStar_Syntax_Subst.compress k in
                             uu____14561.FStar_Syntax_Syntax.n in
                           (uu____14560, args) in
                         match uu____14553 with
                         | (uu____14574,[]) ->
                             let uu____14577 =
                               let uu____14588 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____14588) in
                             FStar_Pervasives_Native.Some uu____14577
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____14609,uu____14610) ->
                             let uu____14635 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____14635 with
                              | (uv1,uv_args) ->
                                  let uu____14690 =
                                    let uu____14691 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14691.FStar_Syntax_Syntax.n in
                                  (match uu____14690 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14703) ->
                                       let uu____14736 =
                                         pat_vars env [] uv_args in
                                       (match uu____14736 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14763  ->
                                                      let uu____14764 =
                                                        let uu____14765 =
                                                          let uu____14766 =
                                                            let uu____14771 =
                                                              let uu____14772
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14772
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14771 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14766 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____14765 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14764)) in
                                            let c1 =
                                              let uu____14782 =
                                                let uu____14783 =
                                                  let uu____14788 =
                                                    let uu____14789 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14789
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____14788 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14783 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14782 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14804 =
                                                let uu____14807 =
                                                  let uu____14808 =
                                                    let uu____14813 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14813
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14808 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14807 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14804 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14831 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14836,uu____14837) ->
                             let uu____14860 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____14860 with
                              | (uv1,uv_args) ->
                                  let uu____14915 =
                                    let uu____14916 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14916.FStar_Syntax_Syntax.n in
                                  (match uu____14915 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14928) ->
                                       let uu____14961 =
                                         pat_vars env [] uv_args in
                                       (match uu____14961 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14988  ->
                                                      let uu____14989 =
                                                        let uu____14990 =
                                                          let uu____14991 =
                                                            let uu____14996 =
                                                              let uu____14997
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14997
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14996 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14991 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____14990 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14989)) in
                                            let c1 =
                                              let uu____15007 =
                                                let uu____15008 =
                                                  let uu____15013 =
                                                    let uu____15014 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____15014
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____15013 in
                                                FStar_Pervasives_Native.fst
                                                  uu____15008 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____15007 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____15029 =
                                                let uu____15032 =
                                                  let uu____15033 =
                                                    let uu____15038 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____15038
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____15033 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15032 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____15029 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____15056 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____15063) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____15108 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____15108
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____15144 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____15144 with
                                  | (args1,rest) ->
                                      let uu____15173 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____15173 with
                                       | (xs2,c2) ->
                                           let uu____15186 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____15186
                                             (fun uu____15210  ->
                                                match uu____15210 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____15250 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____15250 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____15322 =
                                        let uu____15327 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____15327 in
                                      FStar_All.pipe_right uu____15322
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____15342 ->
                             let uu____15349 =
                               let uu____15350 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____15351 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____15352 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____15350 uu____15351 uu____15352 in
                             failwith uu____15349 in
                       let uu____15359 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____15359
                         (fun uu____15414  ->
                            match uu____15414 with
                            | (xs1,c1) ->
                                let uu____15463 =
                                  let uu____15504 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____15504) in
                                FStar_Pervasives_Native.Some uu____15463)) in
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
                     let uu____15622 = imitate orig env wl1 st in
                     match uu____15622 with
                     | Failed uu____15627 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____15635 = project orig env wl1 i st in
                      match uu____15635 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____15643) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____15661 = FStar_Syntax_Util.head_and_args t21 in
                match uu____15661 with
                | (hd1,uu____15681) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15710 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15725 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15726 -> true
                     | uu____15745 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____15749 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____15749
                         then true
                         else
                           ((let uu____15752 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____15752
                             then
                               let uu____15753 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____15753
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____15762 =
                    let uu____15767 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____15767
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____15762 FStar_Syntax_Free.names in
                let uu____15828 = FStar_Util.set_is_empty fvs_hd in
                if uu____15828
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____15839 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____15839 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15852 =
                            let uu____15853 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____15853 in
                          giveup_or_defer1 orig uu____15852
                        else
                          (let uu____15855 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____15855
                           then
                             let uu____15856 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____15856
                              then
                                let uu____15857 = subterms args_lhs in
                                imitate' orig env wl1 uu____15857
                              else
                                ((let uu____15862 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____15862
                                  then
                                    let uu____15863 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____15864 = names_to_string fvs1 in
                                    let uu____15865 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15863 uu____15864 uu____15865
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____15872 ->
                                        let uu____15873 = sn_binders env vars in
                                        u_abs k_uv uu____15873 t21 in
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
                               (let uu____15887 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____15887
                                then
                                  ((let uu____15889 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____15889
                                    then
                                      let uu____15890 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____15891 = names_to_string fvs1 in
                                      let uu____15892 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____15890 uu____15891 uu____15892
                                    else ());
                                   (let uu____15894 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs)
                                      uu____15894 (- (Prims.parse_int "1"))))
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
                        let uu____15908 = FStar_Syntax_Free.names t1 in
                        check_head uu____15908 t2 in
                      if uu____15907
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____15913 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____15913
                          then
                            let uu____15914 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____15914
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____15917 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____15917 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____15976 =
               match uu____15976 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k in
                   let uu____16032 = FStar_Syntax_Util.arrow_formals k1 in
                   (match uu____16032 with
                    | (all_formals,uu____16052) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____16219  ->
                                        match uu____16219 with
                                        | (x,imp) ->
                                            let uu____16230 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____16230, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____16243 = FStar_Syntax_Util.type_u () in
                                match uu____16243 with
                                | (t1,uu____16249) ->
                                    let uu____16250 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    FStar_Pervasives_Native.fst uu____16250 in
                              let uu____16255 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____16255 with
                               | (t',tm_u1) ->
                                   let uu____16266 = destruct_flex_t t' in
                                   (match uu____16266 with
                                    | (uu____16309,u1,k11,uu____16312) ->
                                        let sol =
                                          let uu____16374 =
                                            let uu____16383 =
                                              u_abs k1 all_formals t' in
                                            ((u, k1), uu____16383) in
                                          TERM uu____16374 in
                                        let t_app =
                                          FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                            pat_args1
                                            FStar_Pervasives_Native.None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____16497 = pat_var_opt env pat_args hd1 in
                              (match uu____16497 with
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
                                              (fun uu____16554  ->
                                                 match uu____16554 with
                                                 | (x,uu____16560) ->
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
                                      let uu____16569 =
                                        let uu____16570 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____16570 in
                                      if uu____16569
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____16576 =
                                           FStar_Util.set_add
                                             (FStar_Pervasives_Native.fst
                                                formal) pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____16576 formals1
                                           tl1)))
                          | uu____16587 -> failwith "Impossible" in
                        let uu____16608 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____16608 all_formals args) in
             let solve_both_pats wl1 uu____16677 uu____16678 r =
               match (uu____16677, uu____16678) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____16896 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____16896
                   then
                     let uu____16897 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____16897
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____16921 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____16921
                       then
                         let uu____16922 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____16923 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____16924 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____16925 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____16926 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____16922 uu____16923 uu____16924 uu____16925
                           uu____16926
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____16992 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____16992 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____17006 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____17006 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____17062 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____17062 in
                                  let uu____17067 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____17067 k3)
                           else
                             (let uu____17071 =
                                let uu____17072 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____17073 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____17074 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____17072 uu____17073 uu____17074 in
                              failwith uu____17071) in
                       let uu____17075 =
                         let uu____17086 =
                           let uu____17101 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____17101 in
                         match uu____17086 with
                         | (bs,k1') ->
                             let uu____17134 =
                               let uu____17149 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____17149 in
                             (match uu____17134 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____17185 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____17185 in
                                  let uu____17194 =
                                    let uu____17199 =
                                      let uu____17200 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____17200.FStar_Syntax_Syntax.n in
                                    let uu____17205 =
                                      let uu____17206 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____17206.FStar_Syntax_Syntax.n in
                                    (uu____17199, uu____17205) in
                                  (match uu____17194 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____17221,uu____17222) ->
                                       (k1', [sub_prob])
                                   | (uu____17229,FStar_Syntax_Syntax.Tm_type
                                      uu____17230) -> (k2', [sub_prob])
                                   | uu____17237 ->
                                       let uu____17242 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____17242 with
                                        | (t,uu____17258) ->
                                            let uu____17259 = new_uvar r zs t in
                                            (match uu____17259 with
                                             | (k_zs,uu____17275) ->
                                                 let kprob =
                                                   let uu____17277 =
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
                                                          _0_64) uu____17277 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____17075 with
                       | (k_u',sub_probs) ->
                           let uu____17302 =
                             let uu____17317 =
                               let uu____17318 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____17318 in
                             let uu____17327 =
                               let uu____17332 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____17332 in
                             let uu____17337 =
                               let uu____17342 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____17342 in
                             (uu____17317, uu____17327, uu____17337) in
                           (match uu____17302 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____17375 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____17375 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____17394 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____17394
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____17398 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____17398 with
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
             let solve_one_pat uu____17451 uu____17452 =
               match (uu____17451, uu____17452) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____17570 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____17570
                     then
                       let uu____17571 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____17572 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____17571 uu____17572
                     else ());
                    (let uu____17574 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____17574
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____17593  ->
                              fun uu____17594  ->
                                match (uu____17593, uu____17594) with
                                | ((a,uu____17612),(t21,uu____17614)) ->
                                    let uu____17623 =
                                      let uu____17628 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____17628
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____17623
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2 in
                       let guard =
                         let uu____17634 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____17634 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____17649 = occurs_check env wl (u1, k1) t21 in
                        match uu____17649 with
                        | (occurs_ok,uu____17657) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____17665 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____17665
                            then
                              let sol =
                                let uu____17667 =
                                  let uu____17676 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____17676) in
                                TERM uu____17667 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____17683 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____17683
                               then
                                 let uu____17684 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____17684 with
                                 | (sol,(uu____17702,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____17716 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____17716
                                       then
                                         let uu____17717 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____17717
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____17724 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____17726 = lhs in
             match uu____17726 with
             | (t1,u1,k1,args1) ->
                 let uu____17731 = rhs in
                 (match uu____17731 with
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
                       | uu____17771 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____17781 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____17781 with
                              | (sol,uu____17793) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____17796 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____17796
                                    then
                                      let uu____17797 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____17797
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____17804 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____17806 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____17806
        then
          let uu____17807 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____17807
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____17811 = FStar_Util.physical_equality t1 t2 in
           if uu____17811
           then
             let uu____17812 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____17812
           else
             ((let uu____17815 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____17815
               then
                 let uu____17816 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____17816
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____17819,uu____17820) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____17821,FStar_Syntax_Syntax.Tm_bvar uu____17822) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___132_17889 =
                     match uu___132_17889 with
                     | [] -> c
                     | bs ->
                         let uu____17915 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____17915 in
                   let uu____17926 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____17926 with
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
                                   let uu____18090 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____18090
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____18092 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____18092))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___133_18180 =
                     match uu___133_18180 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____18220 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____18220 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____18378 =
                                   let uu____18383 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____18384 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____18383
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____18384 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____18378))
               | (FStar_Syntax_Syntax.Tm_abs uu____18389,uu____18390) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____18421 -> true
                     | uu____18440 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____18488 =
                     let uu____18509 = maybe_eta t1 in
                     let uu____18518 = maybe_eta t2 in
                     (uu____18509, uu____18518) in
                   (match uu____18488 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_18578 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_18578.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_18578.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_18578.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_18578.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_18578.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_18578.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_18578.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_18578.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____18613 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____18613
                        then
                          let uu____18614 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____18614 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____18652 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____18652
                        then
                          let uu____18653 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____18653 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____18661 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____18682,FStar_Syntax_Syntax.Tm_abs uu____18683) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____18714 -> true
                     | uu____18733 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____18781 =
                     let uu____18802 = maybe_eta t1 in
                     let uu____18811 = maybe_eta t2 in
                     (uu____18802, uu____18811) in
                   (match uu____18781 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_18871 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_18871.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_18871.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_18871.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_18871.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_18871.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_18871.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_18871.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_18871.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____18906 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____18906
                        then
                          let uu____18907 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____18907 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____18945 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____18945
                        then
                          let uu____18946 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____18946 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____18954 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____18975,FStar_Syntax_Syntax.Tm_refine uu____18976) ->
                   let uu____18993 = as_refinement env wl t1 in
                   (match uu____18993 with
                    | (x1,phi1) ->
                        let uu____19000 = as_refinement env wl t2 in
                        (match uu____19000 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____19008 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____19008 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____19048 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____19048
                                 (guard_on_element wl problem x11) in
                             let fallback uu____19052 =
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
                                 let uu____19060 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____19060 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____19071 =
                                   let uu____19076 =
                                     let uu____19077 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____19077 :: (p_scope orig) in
                                   mk_problem uu____19076 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____19071 in
                               let uu____19082 =
                                 solve env1
                                   (let uu___167_19084 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___167_19084.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___167_19084.smt_ok);
                                      tcenv = (uu___167_19084.tcenv)
                                    }) in
                               (match uu____19082 with
                                | Failed uu____19091 -> fallback ()
                                | Success uu____19096 ->
                                    let guard =
                                      let uu____19102 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____19107 =
                                        let uu____19108 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____19108
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____19102
                                        uu____19107 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___168_19119 = wl1 in
                                      {
                                        attempting =
                                          (uu___168_19119.attempting);
                                        wl_deferred =
                                          (uu___168_19119.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___168_19119.defer_ok);
                                        smt_ok = (uu___168_19119.smt_ok);
                                        tcenv = (uu___168_19119.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____19121,FStar_Syntax_Syntax.Tm_uvar uu____19122) ->
                   let uu____19163 = destruct_flex_t t1 in
                   let uu____19164 = destruct_flex_t t2 in
                   flex_flex1 orig uu____19163 uu____19164
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19165;
                     FStar_Syntax_Syntax.tk = uu____19166;
                     FStar_Syntax_Syntax.pos = uu____19167;
                     FStar_Syntax_Syntax.vars = uu____19168;_},uu____19169),FStar_Syntax_Syntax.Tm_uvar
                  uu____19170) ->
                   let uu____19239 = destruct_flex_t t1 in
                   let uu____19240 = destruct_flex_t t2 in
                   flex_flex1 orig uu____19239 uu____19240
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____19241,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19242;
                     FStar_Syntax_Syntax.tk = uu____19243;
                     FStar_Syntax_Syntax.pos = uu____19244;
                     FStar_Syntax_Syntax.vars = uu____19245;_},uu____19246))
                   ->
                   let uu____19315 = destruct_flex_t t1 in
                   let uu____19316 = destruct_flex_t t2 in
                   flex_flex1 orig uu____19315 uu____19316
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19317;
                     FStar_Syntax_Syntax.tk = uu____19318;
                     FStar_Syntax_Syntax.pos = uu____19319;
                     FStar_Syntax_Syntax.vars = uu____19320;_},uu____19321),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19322;
                     FStar_Syntax_Syntax.tk = uu____19323;
                     FStar_Syntax_Syntax.pos = uu____19324;
                     FStar_Syntax_Syntax.vars = uu____19325;_},uu____19326))
                   ->
                   let uu____19423 = destruct_flex_t t1 in
                   let uu____19424 = destruct_flex_t t2 in
                   flex_flex1 orig uu____19423 uu____19424
               | (FStar_Syntax_Syntax.Tm_uvar uu____19425,uu____19426) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____19447 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____19447 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19454;
                     FStar_Syntax_Syntax.tk = uu____19455;
                     FStar_Syntax_Syntax.pos = uu____19456;
                     FStar_Syntax_Syntax.vars = uu____19457;_},uu____19458),uu____19459)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____19508 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____19508 t2 wl
               | (uu____19515,FStar_Syntax_Syntax.Tm_uvar uu____19516) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____19537,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19538;
                     FStar_Syntax_Syntax.tk = uu____19539;
                     FStar_Syntax_Syntax.pos = uu____19540;
                     FStar_Syntax_Syntax.vars = uu____19541;_},uu____19542))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____19591,FStar_Syntax_Syntax.Tm_type uu____19592) ->
                   solve_t' env
                     (let uu___169_19614 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_19614.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_19614.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_19614.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_19614.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_19614.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_19614.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_19614.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_19614.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_19614.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19615;
                     FStar_Syntax_Syntax.tk = uu____19616;
                     FStar_Syntax_Syntax.pos = uu____19617;
                     FStar_Syntax_Syntax.vars = uu____19618;_},uu____19619),FStar_Syntax_Syntax.Tm_type
                  uu____19620) ->
                   solve_t' env
                     (let uu___169_19670 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_19670.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_19670.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_19670.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_19670.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_19670.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_19670.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_19670.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_19670.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_19670.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____19671,FStar_Syntax_Syntax.Tm_arrow uu____19672) ->
                   solve_t' env
                     (let uu___169_19708 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_19708.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_19708.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_19708.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_19708.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_19708.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_19708.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_19708.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_19708.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_19708.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19709;
                     FStar_Syntax_Syntax.tk = uu____19710;
                     FStar_Syntax_Syntax.pos = uu____19711;
                     FStar_Syntax_Syntax.vars = uu____19712;_},uu____19713),FStar_Syntax_Syntax.Tm_arrow
                  uu____19714) ->
                   solve_t' env
                     (let uu___169_19778 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_19778.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_19778.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_19778.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_19778.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_19778.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_19778.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_19778.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_19778.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_19778.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____19779,uu____19780) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____19803 =
                        let uu____19804 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____19804 in
                      if uu____19803
                      then
                        let uu____19805 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___170_19811 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_19811.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_19811.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_19811.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_19811.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_19811.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_19811.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_19811.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_19811.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_19811.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____19812 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____19805 uu____19812 t2
                          wl
                      else
                        (let uu____19820 = base_and_refinement env wl t2 in
                         match uu____19820 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____19877 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___171_19883 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_19883.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_19883.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_19883.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_19883.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_19883.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_19883.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_19883.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_19883.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_19883.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____19884 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____19877
                                    uu____19884 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___172_19910 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_19910.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_19910.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____19913 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____19913 in
                                  let guard =
                                    let uu____19927 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____19927
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19937;
                     FStar_Syntax_Syntax.tk = uu____19938;
                     FStar_Syntax_Syntax.pos = uu____19939;
                     FStar_Syntax_Syntax.vars = uu____19940;_},uu____19941),uu____19942)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____19993 =
                        let uu____19994 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____19994 in
                      if uu____19993
                      then
                        let uu____19995 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___170_20001 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_20001.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_20001.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_20001.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_20001.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_20001.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_20001.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_20001.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_20001.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_20001.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____20002 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____19995 uu____20002 t2
                          wl
                      else
                        (let uu____20010 = base_and_refinement env wl t2 in
                         match uu____20010 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____20067 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___171_20073 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_20073.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_20073.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_20073.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_20073.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_20073.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_20073.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_20073.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_20073.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_20073.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____20074 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____20067
                                    uu____20074 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___172_20100 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_20100.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_20100.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____20103 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____20103 in
                                  let guard =
                                    let uu____20117 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____20117
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____20127,FStar_Syntax_Syntax.Tm_uvar uu____20128) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____20150 = base_and_refinement env wl t1 in
                      match uu____20150 with
                      | (t_base,uu____20170) ->
                          solve_t env
                            (let uu___173_20200 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_20200.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_20200.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_20200.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_20200.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_20200.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_20200.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_20200.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_20200.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____20205,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____20206;
                     FStar_Syntax_Syntax.tk = uu____20207;
                     FStar_Syntax_Syntax.pos = uu____20208;
                     FStar_Syntax_Syntax.vars = uu____20209;_},uu____20210))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____20260 = base_and_refinement env wl t1 in
                      match uu____20260 with
                      | (t_base,uu____20280) ->
                          solve_t env
                            (let uu___173_20310 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_20310.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_20310.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_20310.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_20310.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_20310.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_20310.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_20310.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_20310.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____20315,uu____20316) ->
                   let t21 =
                     let uu____20330 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____20330 in
                   solve_t env
                     (let uu___174_20356 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_20356.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___174_20356.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___174_20356.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___174_20356.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_20356.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_20356.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_20356.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_20356.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_20356.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____20357,FStar_Syntax_Syntax.Tm_refine uu____20358) ->
                   let t11 =
                     let uu____20372 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____20372 in
                   solve_t env
                     (let uu___175_20398 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_20398.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_20398.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_20398.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_20398.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_20398.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_20398.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_20398.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_20398.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_20398.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____20403,uu____20404) ->
                   let head1 =
                     let uu____20438 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20438
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20498 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20498
                       FStar_Pervasives_Native.fst in
                   let uu____20553 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20553
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20568 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20568
                      then
                        let guard =
                          let uu____20580 =
                            let uu____20581 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20581 = FStar_Syntax_Util.Equal in
                          if uu____20580
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20585 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____20585) in
                        let uu____20588 = solve_prob orig guard [] wl in
                        solve env uu____20588
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____20591,uu____20592) ->
                   let head1 =
                     let uu____20606 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20606
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20666 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20666
                       FStar_Pervasives_Native.fst in
                   let uu____20721 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20721
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20736 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20736
                      then
                        let guard =
                          let uu____20748 =
                            let uu____20749 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20749 = FStar_Syntax_Util.Equal in
                          if uu____20748
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20753 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____20753) in
                        let uu____20756 = solve_prob orig guard [] wl in
                        solve env uu____20756
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____20759,uu____20760) ->
                   let head1 =
                     let uu____20766 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20766
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20826 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20826
                       FStar_Pervasives_Native.fst in
                   let uu____20881 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20881
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20896 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20896
                      then
                        let guard =
                          let uu____20908 =
                            let uu____20909 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20909 = FStar_Syntax_Util.Equal in
                          if uu____20908
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20913 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____20913) in
                        let uu____20916 = solve_prob orig guard [] wl in
                        solve env uu____20916
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____20919,uu____20920) ->
                   let head1 =
                     let uu____20926 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20926
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20986 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20986
                       FStar_Pervasives_Native.fst in
                   let uu____21041 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____21041
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____21056 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____21056
                      then
                        let guard =
                          let uu____21068 =
                            let uu____21069 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____21069 = FStar_Syntax_Util.Equal in
                          if uu____21068
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____21073 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____21073) in
                        let uu____21076 = solve_prob orig guard [] wl in
                        solve env uu____21076
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____21079,uu____21080) ->
                   let head1 =
                     let uu____21086 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____21086
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____21146 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____21146
                       FStar_Pervasives_Native.fst in
                   let uu____21201 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____21201
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____21216 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____21216
                      then
                        let guard =
                          let uu____21228 =
                            let uu____21229 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____21229 = FStar_Syntax_Util.Equal in
                          if uu____21228
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____21233 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____21233) in
                        let uu____21236 = solve_prob orig guard [] wl in
                        solve env uu____21236
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____21239,uu____21240) ->
                   let head1 =
                     let uu____21264 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____21264
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____21324 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____21324
                       FStar_Pervasives_Native.fst in
                   let uu____21379 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____21379
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____21394 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____21394
                      then
                        let guard =
                          let uu____21406 =
                            let uu____21407 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____21407 = FStar_Syntax_Util.Equal in
                          if uu____21406
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____21411 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____21411) in
                        let uu____21414 = solve_prob orig guard [] wl in
                        solve env uu____21414
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____21417,FStar_Syntax_Syntax.Tm_match uu____21418) ->
                   let head1 =
                     let uu____21452 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____21452
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____21512 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____21512
                       FStar_Pervasives_Native.fst in
                   let uu____21567 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____21567
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____21582 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____21582
                      then
                        let guard =
                          let uu____21594 =
                            let uu____21595 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____21595 = FStar_Syntax_Util.Equal in
                          if uu____21594
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____21599 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____21599) in
                        let uu____21602 = solve_prob orig guard [] wl in
                        solve env uu____21602
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____21605,FStar_Syntax_Syntax.Tm_uinst uu____21606) ->
                   let head1 =
                     let uu____21620 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____21620
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____21680 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____21680
                       FStar_Pervasives_Native.fst in
                   let uu____21735 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____21735
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____21750 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____21750
                      then
                        let guard =
                          let uu____21762 =
                            let uu____21763 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____21763 = FStar_Syntax_Util.Equal in
                          if uu____21762
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____21767 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____21767) in
                        let uu____21770 = solve_prob orig guard [] wl in
                        solve env uu____21770
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____21773,FStar_Syntax_Syntax.Tm_name uu____21774) ->
                   let head1 =
                     let uu____21780 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____21780
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____21840 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____21840
                       FStar_Pervasives_Native.fst in
                   let uu____21895 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____21895
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____21910 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____21910
                      then
                        let guard =
                          let uu____21922 =
                            let uu____21923 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____21923 = FStar_Syntax_Util.Equal in
                          if uu____21922
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____21927 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____21927) in
                        let uu____21930 = solve_prob orig guard [] wl in
                        solve env uu____21930
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____21933,FStar_Syntax_Syntax.Tm_constant uu____21934) ->
                   let head1 =
                     let uu____21940 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____21940
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____22000 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____22000
                       FStar_Pervasives_Native.fst in
                   let uu____22055 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____22055
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____22070 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____22070
                      then
                        let guard =
                          let uu____22082 =
                            let uu____22083 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____22083 = FStar_Syntax_Util.Equal in
                          if uu____22082
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____22087 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____22087) in
                        let uu____22090 = solve_prob orig guard [] wl in
                        solve env uu____22090
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____22093,FStar_Syntax_Syntax.Tm_fvar uu____22094) ->
                   let head1 =
                     let uu____22100 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____22100
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____22160 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____22160
                       FStar_Pervasives_Native.fst in
                   let uu____22215 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____22215
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____22230 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____22230
                      then
                        let guard =
                          let uu____22242 =
                            let uu____22243 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____22243 = FStar_Syntax_Util.Equal in
                          if uu____22242
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____22247 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____22247) in
                        let uu____22250 = solve_prob orig guard [] wl in
                        solve env uu____22250
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____22253,FStar_Syntax_Syntax.Tm_app uu____22254) ->
                   let head1 =
                     let uu____22278 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____22278
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____22338 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____22338
                       FStar_Pervasives_Native.fst in
                   let uu____22393 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____22393
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____22408 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____22408
                      then
                        let guard =
                          let uu____22420 =
                            let uu____22421 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____22421 = FStar_Syntax_Util.Equal in
                          if uu____22420
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____22425 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____22425) in
                        let uu____22428 = solve_prob orig guard [] wl in
                        solve env uu____22428
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____22432,uu____22433),uu____22434) ->
                   solve_t' env
                     (let uu___176_22492 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_22492.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___176_22492.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___176_22492.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___176_22492.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_22492.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_22492.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_22492.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_22492.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_22492.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____22497,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____22499,uu____22500)) ->
                   solve_t' env
                     (let uu___177_22558 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___177_22558.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___177_22558.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___177_22558.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___177_22558.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___177_22558.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___177_22558.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___177_22558.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___177_22558.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___177_22558.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____22559,uu____22560) ->
                   let uu____22575 =
                     let uu____22576 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____22577 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____22576
                       uu____22577 in
                   failwith uu____22575
               | (FStar_Syntax_Syntax.Tm_meta uu____22578,uu____22579) ->
                   let uu____22588 =
                     let uu____22589 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____22590 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____22589
                       uu____22590 in
                   failwith uu____22588
               | (FStar_Syntax_Syntax.Tm_delayed uu____22591,uu____22592) ->
                   let uu____22621 =
                     let uu____22622 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____22623 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____22622
                       uu____22623 in
                   failwith uu____22621
               | (uu____22624,FStar_Syntax_Syntax.Tm_meta uu____22625) ->
                   let uu____22634 =
                     let uu____22635 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____22636 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____22635
                       uu____22636 in
                   failwith uu____22634
               | (uu____22637,FStar_Syntax_Syntax.Tm_delayed uu____22638) ->
                   let uu____22667 =
                     let uu____22668 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____22669 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____22668
                       uu____22669 in
                   failwith uu____22667
               | (uu____22670,FStar_Syntax_Syntax.Tm_let uu____22671) ->
                   let uu____22686 =
                     let uu____22687 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____22688 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____22687
                       uu____22688 in
                   failwith uu____22686
               | uu____22689 -> giveup env "head tag mismatch" orig)))
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
          (let uu____22725 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____22725
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____22745  ->
                  fun uu____22746  ->
                    match (uu____22745, uu____22746) with
                    | ((a1,uu____22764),(a2,uu____22766)) ->
                        let uu____22775 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_88  -> FStar_TypeChecker_Common.TProb _0_88)
                          uu____22775)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____22785 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p)
                      FStar_Pervasives_Native.fst) sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____22785 in
           let wl1 =
             solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____22809 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____22820)::[] -> wp1
              | uu____22845 ->
                  let uu____22856 =
                    let uu____22857 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____22857 in
                  failwith uu____22856 in
            let uu____22862 =
              let uu____22873 =
                let uu____22874 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____22874 in
              [uu____22873] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____22862;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____22875 = lift_c1 () in solve_eq uu____22875 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___134_22881  ->
                       match uu___134_22881 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____22882 -> false)) in
             let uu____22883 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____22929)::uu____22930,(wp2,uu____22932)::uu____22933)
                   -> (wp1, wp2)
               | uu____23014 ->
                   let uu____23039 =
                     let uu____23040 =
                       let uu____23045 =
                         let uu____23046 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____23047 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____23046 uu____23047 in
                       (uu____23045, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____23040 in
                   raise uu____23039 in
             match uu____22883 with
             | (wpc1,wpc2) ->
                 let uu____23078 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____23078
                 then
                   let uu____23083 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____23083 wl
                 else
                   (let uu____23089 =
                      let uu____23096 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____23096 in
                    match uu____23089 with
                    | (c2_decl,qualifiers) ->
                        let uu____23117 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____23117
                        then
                          let c1_repr =
                            let uu____23121 =
                              let uu____23122 =
                                let uu____23123 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____23123 in
                              let uu____23124 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____23122 uu____23124 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____23121 in
                          let c2_repr =
                            let uu____23126 =
                              let uu____23127 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____23128 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____23127 uu____23128 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____23126 in
                          let prob =
                            let uu____23130 =
                              let uu____23135 =
                                let uu____23136 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____23137 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____23136
                                  uu____23137 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____23135 in
                            FStar_TypeChecker_Common.TProb uu____23130 in
                          let wl1 =
                            let uu____23139 =
                              let uu____23142 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____23142 in
                            solve_prob orig uu____23139 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____23151 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____23151
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____23153 =
                                     let uu____23158 =
                                       let uu____23159 =
                                         let uu____23178 =
                                           let uu____23179 =
                                             let uu____23180 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____23180] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____23179 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____23181 =
                                           let uu____23184 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____23185 =
                                             let uu____23188 =
                                               let uu____23189 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____23189 in
                                             [uu____23188] in
                                           uu____23184 :: uu____23185 in
                                         (uu____23178, uu____23181) in
                                       FStar_Syntax_Syntax.Tm_app uu____23159 in
                                     FStar_Syntax_Syntax.mk uu____23158 in
                                   uu____23153
                                     (FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____23197 =
                                    let uu____23202 =
                                      let uu____23203 =
                                        let uu____23222 =
                                          let uu____23223 =
                                            let uu____23224 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____23224] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____23223 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____23225 =
                                          let uu____23228 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____23229 =
                                            let uu____23232 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____23233 =
                                              let uu____23236 =
                                                let uu____23237 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____23237 in
                                              [uu____23236] in
                                            uu____23232 :: uu____23233 in
                                          uu____23228 :: uu____23229 in
                                        (uu____23222, uu____23225) in
                                      FStar_Syntax_Syntax.Tm_app uu____23203 in
                                    FStar_Syntax_Syntax.mk uu____23202 in
                                  uu____23197
                                    (FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____23245 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____23245 in
                           let wl1 =
                             let uu____23255 =
                               let uu____23258 =
                                 let uu____23263 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____23263 g in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____23258 in
                             solve_prob orig uu____23255 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____23282 = FStar_Util.physical_equality c1 c2 in
        if uu____23282
        then
          let uu____23283 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____23283
        else
          ((let uu____23286 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____23286
            then
              let uu____23287 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____23288 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____23287
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____23288
            else ());
           (let uu____23290 =
              let uu____23295 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____23296 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____23295, uu____23296) in
            match uu____23290 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____23300),FStar_Syntax_Syntax.Total
                    (t2,uu____23302)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____23327 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____23327 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____23332,FStar_Syntax_Syntax.Total uu____23333) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____23355),FStar_Syntax_Syntax.Total
                    (t2,uu____23357)) ->
                     let uu____23382 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____23382 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____23388),FStar_Syntax_Syntax.GTotal
                    (t2,uu____23390)) ->
                     let uu____23415 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____23415 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____23421),FStar_Syntax_Syntax.GTotal
                    (t2,uu____23423)) ->
                     let uu____23448 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____23448 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____23453,FStar_Syntax_Syntax.Comp uu____23454) ->
                     let uu____23465 =
                       let uu___178_23470 = problem in
                       let uu____23475 =
                         let uu____23476 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23476 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_23470.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____23475;
                         FStar_TypeChecker_Common.relation =
                           (uu___178_23470.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___178_23470.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___178_23470.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_23470.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_23470.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_23470.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_23470.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_23470.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____23465 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____23477,FStar_Syntax_Syntax.Comp uu____23478) ->
                     let uu____23489 =
                       let uu___178_23494 = problem in
                       let uu____23499 =
                         let uu____23500 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23500 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_23494.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____23499;
                         FStar_TypeChecker_Common.relation =
                           (uu___178_23494.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___178_23494.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___178_23494.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_23494.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_23494.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_23494.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_23494.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_23494.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____23489 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23501,FStar_Syntax_Syntax.GTotal uu____23502) ->
                     let uu____23513 =
                       let uu___179_23518 = problem in
                       let uu____23523 =
                         let uu____23524 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23524 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_23518.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___179_23518.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___179_23518.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____23523;
                         FStar_TypeChecker_Common.element =
                           (uu___179_23518.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_23518.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_23518.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_23518.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_23518.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_23518.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____23513 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23525,FStar_Syntax_Syntax.Total uu____23526) ->
                     let uu____23537 =
                       let uu___179_23542 = problem in
                       let uu____23547 =
                         let uu____23548 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23548 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_23542.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___179_23542.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___179_23542.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____23547;
                         FStar_TypeChecker_Common.element =
                           (uu___179_23542.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_23542.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_23542.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_23542.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_23542.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_23542.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____23537 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23549,FStar_Syntax_Syntax.Comp uu____23550) ->
                     let uu____23551 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____23551
                     then
                       let uu____23552 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____23552 wl
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
                           (let uu____23564 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____23564
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____23566 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____23566 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____23569 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____23571 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____23571) in
                                if uu____23569
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
                                  (let uu____23574 =
                                     let uu____23575 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____23576 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____23575 uu____23576 in
                                   giveup env uu____23574 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____23582 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____23620  ->
              match uu____23620 with
              | (uu____23633,uu____23634,u,uu____23636,uu____23637,uu____23638)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____23582 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____23670 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____23670 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____23688 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____23716  ->
                match uu____23716 with
                | (u1,u2) ->
                    let uu____23723 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____23724 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____23723 uu____23724)) in
      FStar_All.pipe_right uu____23688 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____23743,[])) -> "{}"
      | uu____23768 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____23785 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____23785
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____23788 =
              FStar_List.map
                (fun uu____23798  ->
                   match uu____23798 with
                   | (uu____23803,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____23788 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____23808 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____23808 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____23857 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____23857
    then
      let uu____23858 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____23859 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____23858
        (rel_to_string rel) uu____23859
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
            let uu____23887 =
              let uu____23890 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____23890 in
            FStar_Syntax_Syntax.new_bv uu____23887 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____23899 =
              let uu____23902 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____23902 in
            let uu____23905 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____23899 uu____23905 in
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
          let uu____23938 = FStar_Options.eager_inference () in
          if uu____23938
          then
            let uu___180_23939 = probs in
            {
              attempting = (uu___180_23939.attempting);
              wl_deferred = (uu___180_23939.wl_deferred);
              ctr = (uu___180_23939.ctr);
              defer_ok = false;
              smt_ok = (uu___180_23939.smt_ok);
              tcenv = (uu___180_23939.tcenv)
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
             (let uu____23951 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____23951
              then
                let uu____23952 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____23952
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
          ((let uu____23964 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____23964
            then
              let uu____23965 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____23965
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f in
            (let uu____23969 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____23969
             then
               let uu____23970 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____23970
             else ());
            (let f2 =
               let uu____23973 =
                 let uu____23974 = FStar_Syntax_Util.unmeta f1 in
                 uu____23974.FStar_Syntax_Syntax.n in
               match uu____23973 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____23980 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___181_23981 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___181_23981.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_23981.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_23981.FStar_TypeChecker_Env.implicits)
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
            let uu____24003 =
              let uu____24004 =
                let uu____24005 =
                  let uu____24006 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____24006
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____24005;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____24004 in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____24003
let with_guard_no_simp env prob dopt =
  match dopt with
  | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some d ->
      let uu____24057 =
        let uu____24058 =
          let uu____24059 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst in
          FStar_All.pipe_right uu____24059
            (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
        {
          FStar_TypeChecker_Env.guard_f = uu____24058;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      FStar_Pervasives_Native.Some uu____24057
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
          (let uu____24101 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____24101
           then
             let uu____24102 = FStar_Syntax_Print.term_to_string t1 in
             let uu____24103 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____24102
               uu____24103
           else ());
          (let prob =
             let uu____24106 =
               let uu____24111 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____24111 in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____24106 in
           let g =
             let uu____24119 =
               let uu____24122 = singleton' env prob smt_ok in
               solve_and_commit env uu____24122
                 (fun uu____24124  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____24119 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____24145 = try_teq true env t1 t2 in
        match uu____24145 with
        | FStar_Pervasives_Native.None  ->
            let uu____24148 =
              let uu____24149 =
                let uu____24154 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____24155 = FStar_TypeChecker_Env.get_range env in
                (uu____24154, uu____24155) in
              FStar_Errors.Error uu____24149 in
            raise uu____24148
        | FStar_Pervasives_Native.Some g ->
            ((let uu____24158 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____24158
              then
                let uu____24159 = FStar_Syntax_Print.term_to_string t1 in
                let uu____24160 = FStar_Syntax_Print.term_to_string t2 in
                let uu____24161 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____24159
                  uu____24160 uu____24161
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
          (let uu____24182 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____24182
           then
             let uu____24183 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____24184 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____24183
               uu____24184
           else ());
          (let uu____24186 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____24186 with
           | (prob,x) ->
               let g =
                 let uu____24198 =
                   let uu____24201 = singleton' env prob smt_ok in
                   solve_and_commit env uu____24201
                     (fun uu____24203  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____24198 in
               ((let uu____24213 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____24213
                 then
                   let uu____24214 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____24215 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____24216 =
                     let uu____24217 = FStar_Util.must g in
                     guard_to_string env uu____24217 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____24214 uu____24215 uu____24216
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
          let uu____24249 = FStar_TypeChecker_Env.get_range env in
          let uu____24250 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____24249 uu____24250
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____24266 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____24266
         then
           let uu____24267 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____24268 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____24267
             uu____24268
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____24273 =
             let uu____24278 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____24278 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____24273 in
         let uu____24283 =
           let uu____24286 = singleton env prob in
           solve_and_commit env uu____24286
             (fun uu____24288  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____24283)
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
      fun uu____24320  ->
        match uu____24320 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____24359 =
                 let uu____24360 =
                   let uu____24365 =
                     let uu____24366 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____24367 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____24366 uu____24367 in
                   let uu____24368 = FStar_TypeChecker_Env.get_range env in
                   (uu____24365, uu____24368) in
                 FStar_Errors.Error uu____24360 in
               raise uu____24359) in
            let equiv1 v1 v' =
              let uu____24376 =
                let uu____24381 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____24382 = FStar_Syntax_Subst.compress_univ v' in
                (uu____24381, uu____24382) in
              match uu____24376 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____24401 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____24431 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____24431 with
                      | FStar_Syntax_Syntax.U_unif uu____24438 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____24467  ->
                                    match uu____24467 with
                                    | (u,v') ->
                                        let uu____24476 = equiv1 v1 v' in
                                        if uu____24476
                                        then
                                          let uu____24479 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____24479 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____24495 -> [])) in
            let uu____24500 =
              let wl =
                let uu___182_24504 = empty_worklist env in
                {
                  attempting = (uu___182_24504.attempting);
                  wl_deferred = (uu___182_24504.wl_deferred);
                  ctr = (uu___182_24504.ctr);
                  defer_ok = false;
                  smt_ok = (uu___182_24504.smt_ok);
                  tcenv = (uu___182_24504.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____24522  ->
                      match uu____24522 with
                      | (lb,v1) ->
                          let uu____24529 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____24529 with
                           | USolved wl1 -> ()
                           | uu____24531 -> fail lb v1))) in
            let rec check_ineq uu____24539 =
              match uu____24539 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____24548) -> true
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
                      uu____24571,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____24573,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____24584) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____24591,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____24599 -> false) in
            let uu____24604 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____24619  ->
                      match uu____24619 with
                      | (u,v1) ->
                          let uu____24626 = check_ineq (u, v1) in
                          if uu____24626
                          then true
                          else
                            ((let uu____24629 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____24629
                              then
                                let uu____24630 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____24631 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____24630
                                  uu____24631
                              else ());
                             false))) in
            if uu____24604
            then ()
            else
              ((let uu____24635 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____24635
                then
                  ((let uu____24637 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____24637);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____24647 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____24647))
                else ());
               (let uu____24657 =
                  let uu____24658 =
                    let uu____24663 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____24663) in
                  FStar_Errors.Error uu____24658 in
                raise uu____24657))
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
      let fail uu____24715 =
        match uu____24715 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____24729 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____24729
       then
         let uu____24730 = wl_to_string wl in
         let uu____24731 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____24730 uu____24731
       else ());
      (let g1 =
         let uu____24746 = solve_and_commit env wl fail in
         match uu____24746 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___183_24759 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___183_24759.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___183_24759.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___183_24759.FStar_TypeChecker_Env.implicits)
             }
         | uu____24764 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___184_24768 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___184_24768.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___184_24768.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___184_24768.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____24785 = FStar_ST.read last_proof_ns in
    match uu____24785 with
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
            let uu___185_24828 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___185_24828.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___185_24828.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___185_24828.FStar_TypeChecker_Env.implicits)
            } in
          let uu____24829 =
            let uu____24830 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____24830 in
          if uu____24829
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____24838 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____24838
                   then
                     let uu____24839 = FStar_TypeChecker_Env.get_range env in
                     let uu____24840 =
                       let uu____24841 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____24841 in
                     FStar_Errors.diag uu____24839 uu____24840
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   let uu____24844 = check_trivial vc1 in
                   match uu____24844 with
                   | FStar_TypeChecker_Common.Trivial  ->
                       FStar_Pervasives_Native.Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then
                         ((let uu____24851 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____24851
                           then
                             let uu____24852 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____24853 =
                               let uu____24854 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1
                                 "Cannot solve without SMT : %s\n"
                                 uu____24854 in
                             FStar_Errors.diag uu____24852 uu____24853
                           else ());
                          FStar_Pervasives_Native.None)
                       else
                         ((let uu____24859 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____24859
                           then
                             let uu____24860 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____24861 =
                               let uu____24862 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____24862 in
                             FStar_Errors.diag uu____24860 uu____24861
                           else ());
                          (let vcs =
                             let uu____24873 = FStar_Options.use_tactics () in
                             if uu____24873
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else
                               (let uu____24883 =
                                  let uu____24890 = FStar_Options.peek () in
                                  (env, vc2, uu____24890) in
                                [uu____24883]) in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____24924  ->
                                   match uu____24924 with
                                   | (env1,goal,opts) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify;
                                           FStar_TypeChecker_Normalize.Primops]
                                           env1 goal in
                                       let uu____24935 = check_trivial goal1 in
                                       (match uu____24935 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____24937 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____24937
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            (FStar_Options.push ();
                                             FStar_Options.set opts;
                                             maybe_update_proof_ns env1;
                                             (let uu____24944 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____24944
                                              then
                                                let uu____24945 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____24946 =
                                                  let uu____24947 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____24948 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____24947 uu____24948 in
                                                FStar_Errors.diag uu____24945
                                                  uu____24946
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
      let uu____24960 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____24960 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____24966 =
            let uu____24967 =
              let uu____24972 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____24972) in
            FStar_Errors.Error uu____24967 in
          raise uu____24966
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____24981 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____24981 with
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
        let uu____24999 = FStar_Syntax_Unionfind.find u in
        match uu____24999 with
        | FStar_Pervasives_Native.None  -> true
        | uu____25002 -> false in
      let rec until_fixpoint acc implicits =
        let uu____25020 = acc in
        match uu____25020 with
        | (out,changed) ->
            (match implicits with
             | [] ->
                 if Prims.op_Negation changed
                 then out
                 else until_fixpoint ([], false) out
             | hd1::tl1 ->
                 let uu____25106 = hd1 in
                 (match uu____25106 with
                  | (uu____25119,env,u,tm,k,r) ->
                      let uu____25125 = unresolved u in
                      if uu____25125
                      then until_fixpoint ((hd1 :: out), changed) tl1
                      else
                        (let env1 =
                           FStar_TypeChecker_Env.set_expected_typ env k in
                         let tm1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta] env1 tm in
                         (let uu____25156 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "RelCheck") in
                          if uu____25156
                          then
                            let uu____25157 =
                              FStar_Syntax_Print.uvar_to_string u in
                            let uu____25158 =
                              FStar_Syntax_Print.term_to_string tm1 in
                            let uu____25159 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print3
                              "Checking uvar %s resolved to %s at type %s\n"
                              uu____25157 uu____25158 uu____25159
                          else ());
                         (let env2 =
                            if forcelax
                            then
                              let uu___186_25162 = env1 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___186_25162.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___186_25162.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___186_25162.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___186_25162.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___186_25162.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___186_25162.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___186_25162.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___186_25162.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___186_25162.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___186_25162.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___186_25162.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___186_25162.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___186_25162.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___186_25162.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___186_25162.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___186_25162.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___186_25162.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___186_25162.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___186_25162.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___186_25162.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___186_25162.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___186_25162.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___186_25162.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___186_25162.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___186_25162.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___186_25162.FStar_TypeChecker_Env.is_native_tactic)
                              }
                            else env1 in
                          let uu____25164 =
                            env2.FStar_TypeChecker_Env.type_of
                              (let uu___187_25172 = env2 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___187_25172.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___187_25172.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___187_25172.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___187_25172.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___187_25172.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___187_25172.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___187_25172.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___187_25172.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___187_25172.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___187_25172.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___187_25172.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___187_25172.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___187_25172.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___187_25172.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___187_25172.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___187_25172.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___187_25172.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___187_25172.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___187_25172.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___187_25172.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___187_25172.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___187_25172.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___187_25172.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___187_25172.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___187_25172.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___187_25172.FStar_TypeChecker_Env.is_native_tactic)
                               }) tm1 in
                          match uu____25164 with
                          | (uu____25173,uu____25174,g1) ->
                              let g2 =
                                if env2.FStar_TypeChecker_Env.is_pattern
                                then
                                  let uu___188_25177 = g1 in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      FStar_TypeChecker_Common.Trivial;
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___188_25177.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___188_25177.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits =
                                      (uu___188_25177.FStar_TypeChecker_Env.implicits)
                                  }
                                else g1 in
                              let g' =
                                let uu____25180 =
                                  discharge_guard'
                                    (FStar_Pervasives_Native.Some
                                       (fun uu____25186  ->
                                          FStar_Syntax_Print.term_to_string
                                            tm1)) env2 g2 true in
                                match uu____25180 with
                                | FStar_Pervasives_Native.Some g3 -> g3
                                | FStar_Pervasives_Native.None  ->
                                    failwith
                                      "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                              until_fixpoint
                                ((FStar_List.append
                                    g'.FStar_TypeChecker_Env.implicits out),
                                  true) tl1)))) in
      let uu___189_25214 = g in
      let uu____25215 =
        until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___189_25214.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___189_25214.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs =
          (uu___189_25214.FStar_TypeChecker_Env.univ_ineqs);
        FStar_TypeChecker_Env.implicits = uu____25215
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
        let uu____25273 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____25273 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____25286 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____25286
      | (reason,uu____25288,uu____25289,e,t,r)::uu____25293 ->
          let uu____25320 =
            let uu____25321 =
              let uu____25326 =
                let uu____25327 = FStar_Syntax_Print.term_to_string t in
                let uu____25328 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____25327 uu____25328 in
              (uu____25326, r) in
            FStar_Errors.Error uu____25321 in
          raise uu____25320
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___190_25337 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___190_25337.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___190_25337.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___190_25337.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25366 = try_teq false env t1 t2 in
        match uu____25366 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____25370 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____25370 with
             | FStar_Pervasives_Native.Some uu____25375 -> true
             | FStar_Pervasives_Native.None  -> false)