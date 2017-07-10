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
        FStar_TypeChecker_Env.univ_ineqs = uu____23;
        FStar_TypeChecker_Env.implicits = uu____24;_} -> true
    | uu____38 -> false
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
            FStar_TypeChecker_Env.deferred = uu____61;
            FStar_TypeChecker_Env.univ_ineqs = uu____62;
            FStar_TypeChecker_Env.implicits = uu____63;_}
          -> g
      | FStar_Pervasives_Native.Some g1 ->
          let f =
            match g1.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.NonTrivial f -> f
            | uu____78 -> failwith "impossible" in
          let uu____79 =
            let uu___135_80 = g1 in
            let uu____81 =
              let uu____82 =
                let uu____83 =
                  let uu____84 = FStar_Syntax_Syntax.mk_binder x in
                  [uu____84] in
                FStar_Syntax_Util.abs uu____83 f
                  (FStar_Pervasives_Native.Some
                     (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0)) in
              FStar_All.pipe_left
                (fun _0_39  -> FStar_TypeChecker_Common.NonTrivial _0_39)
                uu____82 in
            {
              FStar_TypeChecker_Env.guard_f = uu____81;
              FStar_TypeChecker_Env.deferred =
                (uu___135_80.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___135_80.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___135_80.FStar_TypeChecker_Env.implicits)
            } in
          FStar_Pervasives_Native.Some uu____79
let apply_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___136_94 = g in
          let uu____95 =
            let uu____96 =
              let uu____97 =
                let uu____100 =
                  let uu____101 =
                    let uu____111 =
                      let uu____113 = FStar_Syntax_Syntax.as_arg e in
                      [uu____113] in
                    (f, uu____111) in
                  FStar_Syntax_Syntax.Tm_app uu____101 in
                FStar_Syntax_Syntax.mk uu____100 in
              uu____97
                (FStar_Pervasives_Native.Some
                   (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun _0_40  -> FStar_TypeChecker_Common.NonTrivial _0_40)
              uu____96 in
          {
            FStar_TypeChecker_Env.guard_f = uu____95;
            FStar_TypeChecker_Env.deferred =
              (uu___136_94.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___136_94.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___136_94.FStar_TypeChecker_Env.implicits)
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
          let uu___137_137 = g in
          let uu____138 =
            let uu____139 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____139 in
          {
            FStar_TypeChecker_Env.guard_f = uu____138;
            FStar_TypeChecker_Env.deferred =
              (uu___137_137.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___137_137.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___137_137.FStar_TypeChecker_Env.implicits)
          }
let trivial: FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____144 -> failwith "impossible"
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
          let uu____157 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____157
let check_trivial:
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula =
  fun t  ->
    let uu____162 =
      let uu____163 = FStar_Syntax_Util.unmeta t in
      uu____163.FStar_Syntax_Syntax.n in
    match uu____162 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____167 -> FStar_TypeChecker_Common.NonTrivial t
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
        let uu____203 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
        {
          FStar_TypeChecker_Env.guard_f = uu____203;
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
                       let uu____259 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____259
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___138_261 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___138_261.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___138_261.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___138_261.FStar_TypeChecker_Env.implicits)
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
               let uu____281 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____281
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
            let uu___139_297 = g in
            let uu____298 =
              let uu____299 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____299 in
            {
              FStar_TypeChecker_Env.guard_f = uu____298;
              FStar_TypeChecker_Env.deferred =
                (uu___139_297.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___139_297.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___139_297.FStar_TypeChecker_Env.implicits)
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
        | uu____330 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____345 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____345 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r in
            let uu____357 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.n)) r in
            (uu____357, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____389 = FStar_Syntax_Util.type_u () in
        match uu____389 with
        | (t_type,u) ->
            let uu____394 =
              let uu____397 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____397 t_type in
            (match uu____394 with
             | (tt,uu____399) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____423 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____451 -> false
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
    match projectee with | Success _0 -> true | uu____601 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____617 -> false
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
    match projectee with | COVARIANT  -> true | uu____636 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____641 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____646 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___107_662  ->
    match uu___107_662 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____678 =
    let uu____679 = FStar_Syntax_Subst.compress t in
    uu____679.FStar_Syntax_Syntax.n in
  match uu____678 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____700 = FStar_Syntax_Print.uvar_to_string u in
      let uu____701 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____700 uu____701
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____704;
         FStar_Syntax_Syntax.pos = uu____705;_},args)
      ->
      let uu____736 = FStar_Syntax_Print.uvar_to_string u in
      let uu____737 = FStar_Syntax_Print.term_to_string ty in
      let uu____738 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" uu____736 uu____737 uu____738
  | uu____739 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___108_747  ->
      match uu___108_747 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____751 =
            let uu____753 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____754 =
              let uu____756 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____757 =
                let uu____759 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____760 =
                  let uu____762 =
                    let uu____764 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____765 =
                      let uu____767 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____768 =
                        let uu____770 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (FStar_Pervasives_Native.fst
                               p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____771 =
                          let uu____773 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____773] in
                        uu____770 :: uu____771 in
                      uu____767 :: uu____768 in
                    uu____764 :: uu____765 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____762 in
                uu____759 :: uu____760 in
              uu____756 :: uu____757 in
            uu____753 :: uu____754 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____751
      | FStar_TypeChecker_Common.CProb p ->
          let uu____778 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____779 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____778
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____779
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___109_787  ->
      match uu___109_787 with
      | UNIV (u,t) ->
          let x =
            let uu____791 = FStar_Options.hide_uvar_nums () in
            if uu____791
            then "?"
            else
              (let uu____793 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____793 FStar_Util.string_of_int) in
          let uu____794 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____794
      | TERM ((u,uu____796),t) ->
          let x =
            let uu____801 = FStar_Options.hide_uvar_nums () in
            if uu____801
            then "?"
            else
              (let uu____803 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____803 FStar_Util.string_of_int) in
          let uu____804 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____804
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____815 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____815 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____824 =
      let uu____826 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____826
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____824 (FStar_String.concat ", ")
let args_to_string args =
  let uu____846 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____857  ->
            match uu____857 with
            | (x,uu____861) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right uu____846 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____867 =
      let uu____868 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____868 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____867;
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
        let uu___140_884 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___140_884.wl_deferred);
          ctr = (uu___140_884.ctr);
          defer_ok = (uu___140_884.defer_ok);
          smt_ok;
          tcenv = (uu___140_884.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___141_914 = empty_worklist env in
  let uu____915 = FStar_List.map FStar_Pervasives_Native.snd g in
  {
    attempting = uu____915;
    wl_deferred = (uu___141_914.wl_deferred);
    ctr = (uu___141_914.ctr);
    defer_ok = false;
    smt_ok = (uu___141_914.smt_ok);
    tcenv = (uu___141_914.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___142_930 = wl in
        {
          attempting = (uu___142_930.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___142_930.ctr);
          defer_ok = (uu___142_930.defer_ok);
          smt_ok = (uu___142_930.smt_ok);
          tcenv = (uu___142_930.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___143_944 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___143_944.wl_deferred);
        ctr = (uu___143_944.ctr);
        defer_ok = (uu___143_944.defer_ok);
        smt_ok = (uu___143_944.smt_ok);
        tcenv = (uu___143_944.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____958 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____958
         then
           let uu____959 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____959
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___110_964  ->
    match uu___110_964 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___144_983 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___144_983.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___144_983.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___144_983.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___144_983.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___144_983.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___144_983.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___144_983.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___111_1008  ->
    match uu___111_1008 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___112_1026  ->
      match uu___112_1026 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___113_1030  ->
    match uu___113_1030 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___114_1040  ->
    match uu___114_1040 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___115_1051  ->
    match uu___115_1051 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___116_1062  ->
    match uu___116_1062 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___117_1074  ->
    match uu___117_1074 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___118_1086  ->
    match uu___118_1086 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___119_1096  ->
    match uu___119_1096 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____1111 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1111 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1127  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1186 = next_pid () in
  let uu____1187 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1186;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1187;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1243 = next_pid () in
  let uu____1244 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1243;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1244;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1293 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1293;
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
        let uu____1353 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1353
        then
          let uu____1354 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1355 = prob_to_string env d in
          let uu____1356 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1354 uu____1355 uu____1356 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1361 -> failwith "impossible" in
           let uu____1362 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1370 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1371 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1370, uu____1371)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1375 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1376 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1375, uu____1376) in
           match uu____1362 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___120_1390  ->
            match uu___120_1390 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1398 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1400),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___121_1417  ->
           match uu___121_1417 with
           | UNIV uu____1419 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1423),t) ->
               let uu____1427 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1427
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
        (fun uu___122_1445  ->
           match uu___122_1445 with
           | UNIV (u',t) ->
               let uu____1449 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1449
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1452 -> FStar_Pervasives_Native.None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1461 =
        let uu____1462 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1462 in
      FStar_Syntax_Subst.compress uu____1461
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1471 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1471
let norm_arg env t =
  let uu____1493 = sn env (FStar_Pervasives_Native.fst t) in
  (uu____1493, (FStar_Pervasives_Native.snd t))
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
           (fun uu____1516  ->
              match uu____1516 with
              | (x,imp) ->
                  let uu____1523 =
                    let uu___145_1524 = x in
                    let uu____1525 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___145_1524.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___145_1524.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1525
                    } in
                  (uu____1523, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1542 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1542
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1545 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1545
        | uu____1547 -> u2 in
      let uu____1548 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1548
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
          (let uu____1664 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____1664 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1676;
               FStar_Syntax_Syntax.pos = uu____1677;_} ->
               ((x1.FStar_Syntax_Syntax.sort),
                 (FStar_Pervasives_Native.Some (x1, phi1)))
           | tt ->
               let uu____1697 =
                 let uu____1698 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1699 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1698
                   uu____1699 in
               failwith uu____1697)
    | FStar_Syntax_Syntax.Tm_uinst uu____1709 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1736 =
             let uu____1737 = FStar_Syntax_Subst.compress t1' in
             uu____1737.FStar_Syntax_Syntax.n in
           match uu____1736 with
           | FStar_Syntax_Syntax.Tm_refine uu____1749 -> aux true t1'
           | uu____1754 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1766 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1789 =
             let uu____1790 = FStar_Syntax_Subst.compress t1' in
             uu____1790.FStar_Syntax_Syntax.n in
           match uu____1789 with
           | FStar_Syntax_Syntax.Tm_refine uu____1802 -> aux true t1'
           | uu____1807 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_app uu____1819 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1851 =
             let uu____1852 = FStar_Syntax_Subst.compress t1' in
             uu____1852.FStar_Syntax_Syntax.n in
           match uu____1851 with
           | FStar_Syntax_Syntax.Tm_refine uu____1864 -> aux true t1'
           | uu____1869 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_type uu____1881 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_constant uu____1893 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_name uu____1905 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1917 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1929 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_abs uu____1948 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1969 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_let uu____1991 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_match uu____2010 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_meta uu____2036 ->
        let uu____2041 =
          let uu____2042 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2043 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2042
            uu____2043 in
        failwith uu____2041
    | FStar_Syntax_Syntax.Tm_ascribed uu____2053 ->
        let uu____2071 =
          let uu____2072 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2073 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2072
            uu____2073 in
        failwith uu____2071
    | FStar_Syntax_Syntax.Tm_delayed uu____2083 ->
        let uu____2098 =
          let uu____2099 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2100 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2099
            uu____2100 in
        failwith uu____2098
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____2110 =
          let uu____2111 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2112 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2111
            uu____2112 in
        failwith uu____2110 in
  let uu____2122 = whnf env t1 in aux false uu____2122
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____2133 =
        let uu____2143 = empty_worklist env in
        base_and_refinement env uu____2143 t in
      FStar_All.pipe_right uu____2133 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2168 = FStar_Syntax_Syntax.null_bv t in
    (uu____2168, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____2192 = base_and_refinement env wl t in
  match uu____2192 with
  | (t_base,refinement) ->
      (match refinement with
       | FStar_Pervasives_Native.None  -> trivial_refinement t_base
       | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
let force_refinement uu____2253 =
  match uu____2253 with
  | (t_base,refopt) ->
      let uu____2267 =
        match refopt with
        | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
        | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
      (match uu____2267 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___123_2293  ->
      match uu___123_2293 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2297 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2298 =
            let uu____2299 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____2299 in
          let uu____2300 =
            let uu____2301 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____2301 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2297 uu____2298
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2300
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2305 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2306 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____2307 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2305 uu____2306
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2307
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2312 =
      let uu____2314 =
        let uu____2316 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2330  ->
                  match uu____2330 with | (uu____2334,uu____2335,x) -> x)) in
        FStar_List.append wl.attempting uu____2316 in
      FStar_List.map (wl_prob_to_string wl) uu____2314 in
    FStar_All.pipe_right uu____2312 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2356 =
          let uu____2366 =
            let uu____2367 = FStar_Syntax_Subst.compress k in
            uu____2367.FStar_Syntax_Syntax.n in
          match uu____2366 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2412 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2412)
              else
                (let uu____2426 = FStar_Syntax_Util.abs_formals t in
                 match uu____2426 with
                 | (ys',t1,uu____2442) ->
                     let uu____2445 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2445))
          | uu____2466 ->
              let uu____2467 =
                let uu____2473 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____2473) in
              ((ys, t), uu____2467) in
        match uu____2356 with
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
                 let uu____2525 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2525 c in
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
            let uu____2553 = p_guard prob in
            match uu____2553 with
            | (uu____2556,uv) ->
                ((let uu____2559 =
                    let uu____2560 = FStar_Syntax_Subst.compress uv in
                    uu____2560.FStar_Syntax_Syntax.n in
                  match uu____2559 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2584 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2584
                        then
                          let uu____2585 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2586 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2587 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2585
                            uu____2586 uu____2587
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2589 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___146_2592 = wl in
                  {
                    attempting = (uu___146_2592.attempting);
                    wl_deferred = (uu___146_2592.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___146_2592.defer_ok);
                    smt_ok = (uu___146_2592.smt_ok);
                    tcenv = (uu___146_2592.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2608 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2608
         then
           let uu____2609 = FStar_Util.string_of_int pid in
           let uu____2610 =
             let uu____2611 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2611 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2609 uu____2610
         else ());
        commit sol;
        (let uu___147_2616 = wl in
         {
           attempting = (uu___147_2616.attempting);
           wl_deferred = (uu___147_2616.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___147_2616.defer_ok);
           smt_ok = (uu___147_2616.smt_ok);
           tcenv = (uu___147_2616.tcenv)
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
            | (uu____2649,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2657 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____2657 in
          (let uu____2663 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2663
           then
             let uu____2664 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2665 =
               let uu____2666 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2666 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2664 uu____2665
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2695 =
    let uu____2699 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2699 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2695
    (FStar_Util.for_some
       (fun uu____2719  ->
          match uu____2719 with
          | (uv,uu____2723) ->
              FStar_Syntax_Unionfind.equiv uv
                (FStar_Pervasives_Native.fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2762 = occurs wl uk t in Prims.op_Negation uu____2762 in
  let msg =
    if occurs_ok
    then FStar_Pervasives_Native.None
    else
      (let uu____2767 =
         let uu____2768 =
           FStar_Syntax_Print.uvar_to_string (FStar_Pervasives_Native.fst uk) in
         let uu____2769 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2768 uu____2769 in
       FStar_Pervasives_Native.Some uu____2767) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2824 = occurs_check env wl uk t in
  match uu____2824 with
  | (occurs_ok,msg) ->
      let uu____2841 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2841, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  ->
            fun x  -> FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2911 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2942  ->
            fun uu____2943  ->
              match (uu____2942, uu____2943) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2986 =
                    let uu____2987 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2987 in
                  if uu____2986
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____3001 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____3001
                     then
                       let uu____3008 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____3008)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2911 with | (isect,uu____3030) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____3093  ->
          fun uu____3094  ->
            match (uu____3093, uu____3094) with
            | ((a,uu____3104),(b,uu____3106)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____3155 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____3164  ->
                match uu____3164 with
                | (b,uu____3168) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____3155
      then FStar_Pervasives_Native.None
      else
        FStar_Pervasives_Native.Some (a, (FStar_Pervasives_Native.snd hd1))
  | uu____3177 -> FStar_Pervasives_Native.None
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
            let uu____3222 = pat_var_opt env seen hd1 in
            (match uu____3222 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____3230 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____3230
                   then
                     let uu____3231 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____3231
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3244 =
      let uu____3245 = FStar_Syntax_Subst.compress t in
      uu____3245.FStar_Syntax_Syntax.n in
    match uu____3244 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3248 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3259;
           FStar_Syntax_Syntax.tk = uu____3260;
           FStar_Syntax_Syntax.pos = uu____3261;_},uu____3262)
        -> true
    | uu____3286 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3358;
         FStar_Syntax_Syntax.pos = uu____3359;_},args)
      -> (t, uv, k, args)
  | uu____3405 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____3466 = destruct_flex_t t in
  match uu____3466 with
  | (t1,uv,k,args) ->
      let uu____3542 = pat_vars env [] args in
      (match uu____3542 with
       | FStar_Pervasives_Native.Some vars ->
           ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
       | uu____3604 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3658 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3683 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3688 -> false
let head_match: match_result -> match_result =
  fun uu___124_3692  ->
    match uu___124_3692 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3701 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3712 ->
          let uu____3713 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3713 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____3719 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____3735 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3741 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____3757 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____3758 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____3759 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____3770 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____3778 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3794) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3800,uu____3801) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3831) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3846;
             FStar_Syntax_Syntax.index = uu____3847;
             FStar_Syntax_Syntax.sort = t2;_},uu____3849)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3856 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3857 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3858 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3866 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3877 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____3877
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
            let uu____3899 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3899
            then FullMatch
            else
              (let uu____3901 =
                 let uu____3906 =
                   let uu____3908 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____3908 in
                 let uu____3909 =
                   let uu____3911 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____3911 in
                 (uu____3906, uu____3909) in
               MisMatch uu____3901)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3915),FStar_Syntax_Syntax.Tm_uinst (g,uu____3917)) ->
            let uu____3926 = head_matches env f g in
            FStar_All.pipe_right uu____3926 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3933),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3935)) ->
            let uu____3968 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____3968
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3973),FStar_Syntax_Syntax.Tm_refine (y,uu____3975)) ->
            let uu____3984 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3984 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3986),uu____3987) ->
            let uu____3992 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3992 head_match
        | (uu____3993,FStar_Syntax_Syntax.Tm_refine (x,uu____3995)) ->
            let uu____4000 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____4000 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____4001,FStar_Syntax_Syntax.Tm_type
           uu____4002) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____4003,FStar_Syntax_Syntax.Tm_arrow uu____4004) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____4020),FStar_Syntax_Syntax.Tm_app (head',uu____4022))
            ->
            let uu____4051 = head_matches env head1 head' in
            FStar_All.pipe_right uu____4051 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____4053),uu____4054) ->
            let uu____4069 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____4069 head_match
        | (uu____4070,FStar_Syntax_Syntax.Tm_app (head1,uu____4072)) ->
            let uu____4087 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____4087 head_match
        | uu____4088 ->
            let uu____4091 =
              let uu____4096 = delta_depth_of_term env t11 in
              let uu____4098 = delta_depth_of_term env t21 in
              (uu____4096, uu____4098) in
            MisMatch uu____4091
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____4139 = FStar_Syntax_Util.head_and_args t in
    match uu____4139 with
    | (head1,uu____4151) ->
        let uu____4166 =
          let uu____4167 = FStar_Syntax_Util.un_uinst head1 in
          uu____4167.FStar_Syntax_Syntax.n in
        (match uu____4166 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____4172 =
               let uu____4173 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____4173 FStar_Option.isSome in
             if uu____4172
             then
               let uu____4183 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____4183
                 (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
             else FStar_Pervasives_Native.None
         | uu____4186 -> FStar_Pervasives_Native.None) in
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
         ),uu____4254)
        ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4264 =
             let uu____4269 = maybe_inline t11 in
             let uu____4271 = maybe_inline t21 in (uu____4269, uu____4271) in
           match uu____4264 with
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
               fail r
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.None )
               -> aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t22)
               -> aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.Some
              t22) -> aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch
        (uu____4292,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Delta_equational ))
        ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4302 =
             let uu____4307 = maybe_inline t11 in
             let uu____4309 = maybe_inline t21 in (uu____4307, uu____4309) in
           match uu____4302 with
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
        let uu____4334 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____4334 with
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
        let uu____4349 =
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
        (match uu____4349 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4364 -> fail r
    | uu____4369 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4399 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4431 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4449 = FStar_Syntax_Util.type_u () in
      match uu____4449 with
      | (t,uu____4453) ->
          let uu____4454 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____4454
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4465 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____4465 FStar_Pervasives_Native.fst
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
        let uu____4509 = head_matches env t1 t' in
        match uu____4509 with
        | MisMatch uu____4510 -> false
        | uu____4515 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4581,imp),T (t2,uu____4584)) -> (t2, imp)
                     | uu____4601 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4644  ->
                    match uu____4644 with
                    | (t2,uu____4652) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____4682 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____4682 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4735))::tcs2) ->
                       aux
                         (((let uu___148_4758 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_4758.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_4758.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4768 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___125_4799 =
                 match uu___125_4799 with
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
               let uu____4862 = decompose1 [] bs1 in
               (rebuild, matches, uu____4862))
      | uu____4890 ->
          let rebuild uu___126_4895 =
            match uu___126_4895 with
            | [] -> t1
            | uu____4897 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___127_4918  ->
    match uu___127_4918 with
    | T (t,uu____4920) -> t
    | uu____4929 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___128_4933  ->
    match uu___128_4933 with
    | T (t,uu____4935) -> FStar_Syntax_Syntax.as_arg t
    | uu____4944 -> failwith "Impossible"
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
              | (uu____5018,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____5037 = new_uvar r scope1 k in
                  (match uu____5037 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____5049 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____5064 =
                         let uu____5065 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____5065 in
                       ((T (gi_xs, mk_kind)), uu____5064))
              | (uu____5074,uu____5075,C uu____5076) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____5158 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____5169;
                         FStar_Syntax_Syntax.pos = uu____5170;_})
                        ->
                        let uu____5184 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____5184 with
                         | (T (gi_xs,uu____5200),prob) ->
                             let uu____5210 =
                               let uu____5211 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____5211 in
                             (uu____5210, [prob])
                         | uu____5213 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____5223;
                         FStar_Syntax_Syntax.pos = uu____5224;_})
                        ->
                        let uu____5238 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____5238 with
                         | (T (gi_xs,uu____5254),prob) ->
                             let uu____5264 =
                               let uu____5265 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____5265 in
                             (uu____5264, [prob])
                         | uu____5267 -> failwith "impossible")
                    | (uu____5273,uu____5274,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____5276;
                         FStar_Syntax_Syntax.pos = uu____5277;_})
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
                        let uu____5351 =
                          let uu____5356 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____5356 FStar_List.unzip in
                        (match uu____5351 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5385 =
                                 let uu____5386 =
                                   let uu____5389 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____5389 un_T in
                                 let uu____5390 =
                                   let uu____5396 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____5396
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5386;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5390;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5385 in
                             ((C gi_xs), sub_probs))
                    | uu____5401 ->
                        let uu____5408 = sub_prob scope1 args q in
                        (match uu____5408 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____5158 with
                   | (tc,probs) ->
                       let uu____5426 =
                         match q with
                         | (FStar_Pervasives_Native.Some
                            b,uu____5452,uu____5453) ->
                             let uu____5461 =
                               let uu____5465 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____5465 :: args in
                             ((FStar_Pervasives_Native.Some b), (b ::
                               scope1), uu____5461)
                         | uu____5483 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____5426 with
                        | (bopt,scope2,args1) ->
                            let uu____5526 = aux scope2 args1 qs2 in
                            (match uu____5526 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5547 =
                                         let uu____5549 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____5549 in
                                       FStar_Syntax_Util.mk_conj_l uu____5547
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____5563 =
                                         let uu____5565 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____5566 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____5565 :: uu____5566 in
                                       FStar_Syntax_Util.mk_conj_l uu____5563 in
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
  let uu___149_5623 = p in
  let uu____5626 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____5627 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___149_5623.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5626;
    FStar_TypeChecker_Common.relation =
      (uu___149_5623.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5627;
    FStar_TypeChecker_Common.element =
      (uu___149_5623.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___149_5623.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___149_5623.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___149_5623.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___149_5623.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___149_5623.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5639 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____5639
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____5644 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5660 = compress_prob wl pr in
        FStar_All.pipe_right uu____5660 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5666 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____5666 with
           | (lh,uu____5679) ->
               let uu____5694 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____5694 with
                | (rh,uu____5707) ->
                    let uu____5722 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5731,FStar_Syntax_Syntax.Tm_uvar uu____5732)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5755,uu____5756)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5769,FStar_Syntax_Syntax.Tm_uvar uu____5770)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5783,uu____5784)
                          ->
                          let uu____5795 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5795 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____5835 ->
                                    let rank =
                                      let uu____5842 = is_top_level_prob prob in
                                      if uu____5842
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5844 =
                                      let uu___150_5847 = tp in
                                      let uu____5850 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___150_5847.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___150_5847.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___150_5847.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5850;
                                        FStar_TypeChecker_Common.element =
                                          (uu___150_5847.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___150_5847.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___150_5847.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___150_5847.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___150_5847.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___150_5847.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5844)))
                      | (uu____5860,FStar_Syntax_Syntax.Tm_uvar uu____5861)
                          ->
                          let uu____5872 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5872 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____5912 ->
                                    let uu____5918 =
                                      let uu___151_5923 = tp in
                                      let uu____5926 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___151_5923.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5926;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___151_5923.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___151_5923.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___151_5923.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___151_5923.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___151_5923.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___151_5923.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___151_5923.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___151_5923.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5918)))
                      | (uu____5942,uu____5943) -> (rigid_rigid, tp) in
                    (match uu____5722 with
                     | (rank,tp1) ->
                         let uu____5954 =
                           FStar_All.pipe_right
                             (let uu___152_5958 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___152_5958.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___152_5958.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___152_5958.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___152_5958.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___152_5958.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___152_5958.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___152_5958.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___152_5958.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___152_5958.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50) in
                         (rank, uu____5954))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5964 =
            FStar_All.pipe_right
              (let uu___153_5968 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___153_5968.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___153_5968.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___153_5968.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___153_5968.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___153_5968.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___153_5968.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___153_5968.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___153_5968.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___153_5968.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51) in
          (rigid_rigid, uu____5964)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____6001 probs =
      match uu____6001 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____6031 = rank wl hd1 in
               (match uu____6031 with
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
    match projectee with | UDeferred _0 -> true | uu____6102 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____6116 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____6130 -> false
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
                        let uu____6173 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____6173 with
                        | (k,uu____6177) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____6183 -> false)))
            | uu____6184 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____6231 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____6231 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____6234 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____6240 =
                     let uu____6241 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____6242 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____6241
                       uu____6242 in
                   UFailed uu____6240)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____6258 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____6258 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____6276 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____6276 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____6279 ->
                let uu____6282 =
                  let uu____6283 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____6284 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____6283
                    uu____6284 msg in
                UFailed uu____6282 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____6285,uu____6286) ->
              let uu____6287 =
                let uu____6288 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6289 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6288 uu____6289 in
              failwith uu____6287
          | (FStar_Syntax_Syntax.U_unknown ,uu____6290) ->
              let uu____6291 =
                let uu____6292 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6293 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6292 uu____6293 in
              failwith uu____6291
          | (uu____6294,FStar_Syntax_Syntax.U_bvar uu____6295) ->
              let uu____6296 =
                let uu____6297 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6298 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6297 uu____6298 in
              failwith uu____6296
          | (uu____6299,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____6300 =
                let uu____6301 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6302 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6301 uu____6302 in
              failwith uu____6300
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____6318 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____6318
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____6332 = occurs_univ v1 u3 in
              if uu____6332
              then
                let uu____6333 =
                  let uu____6334 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6335 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6334 uu____6335 in
                try_umax_components u11 u21 uu____6333
              else
                (let uu____6337 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6337)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____6349 = occurs_univ v1 u3 in
              if uu____6349
              then
                let uu____6350 =
                  let uu____6351 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6352 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6351 uu____6352 in
                try_umax_components u11 u21 uu____6350
              else
                (let uu____6354 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6354)
          | (FStar_Syntax_Syntax.U_max uu____6359,uu____6360) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6365 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6365
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____6367,FStar_Syntax_Syntax.U_max uu____6368) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6373 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6373
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6375,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6376,FStar_Syntax_Syntax.U_name
             uu____6377) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6378) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6379) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6380,FStar_Syntax_Syntax.U_succ
             uu____6381) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6382,FStar_Syntax_Syntax.U_zero
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
  let uu____6452 = bc1 in
  match uu____6452 with
  | (bs1,mk_cod1) ->
      let uu____6477 = bc2 in
      (match uu____6477 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6524 = FStar_Util.first_N n1 bs in
             match uu____6524 with
             | (bs3,rest) ->
                 let uu____6538 = mk_cod rest in (bs3, uu____6538) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____6562 =
               let uu____6566 = mk_cod1 [] in (bs1, uu____6566) in
             let uu____6568 =
               let uu____6572 = mk_cod2 [] in (bs2, uu____6572) in
             (uu____6562, uu____6568)
           else
             if l1 > l2
             then
               (let uu____6599 = curry l2 bs1 mk_cod1 in
                let uu____6609 =
                  let uu____6613 = mk_cod2 [] in (bs2, uu____6613) in
                (uu____6599, uu____6609))
             else
               (let uu____6622 =
                  let uu____6626 = mk_cod1 [] in (bs1, uu____6626) in
                let uu____6628 = curry l1 bs2 mk_cod2 in
                (uu____6622, uu____6628)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6735 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____6735
       then
         let uu____6736 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6736
       else ());
      (let uu____6738 = next_prob probs in
       match uu____6738 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___154_6751 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___154_6751.wl_deferred);
               ctr = (uu___154_6751.ctr);
               defer_ok = (uu___154_6751.defer_ok);
               smt_ok = (uu___154_6751.smt_ok);
               tcenv = (uu___154_6751.tcenv)
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
                  let uu____6758 = solve_flex_rigid_join env tp probs1 in
                  (match uu____6758 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6762 = solve_rigid_flex_meet env tp probs1 in
                     match uu____6762 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____6766,uu____6767) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6776 ->
                let uu____6781 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6813  ->
                          match uu____6813 with
                          | (c,uu____6818,uu____6819) -> c < probs.ctr)) in
                (match uu____6781 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6841 =
                            FStar_List.map
                              (fun uu____6851  ->
                                 match uu____6851 with
                                 | (uu____6857,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____6841
                      | uu____6860 ->
                          let uu____6865 =
                            let uu___155_6866 = probs in
                            let uu____6867 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6880  ->
                                      match uu____6880 with
                                      | (uu____6884,uu____6885,y) -> y)) in
                            {
                              attempting = uu____6867;
                              wl_deferred = rest;
                              ctr = (uu___155_6866.ctr);
                              defer_ok = (uu___155_6866.defer_ok);
                              smt_ok = (uu___155_6866.smt_ok);
                              tcenv = (uu___155_6866.tcenv)
                            } in
                          solve env uu____6865))))
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
            let uu____6892 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____6892 with
            | USolved wl1 ->
                let uu____6894 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____6894
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
                  let uu____6928 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6928 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6931 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6939;
                  FStar_Syntax_Syntax.pos = uu____6940;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6943;
                  FStar_Syntax_Syntax.pos = uu____6944;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6955,uu____6956) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6961,FStar_Syntax_Syntax.Tm_uinst uu____6962) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6967 -> USolved wl
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
            ((let uu____6975 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6975
              then
                let uu____6976 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6976 msg
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
        (let uu____6984 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6984
         then
           let uu____6985 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6985
         else ());
        (let uu____6987 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6987 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____7029 = head_matches_delta env () t1 t2 in
               match uu____7029 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____7051 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____7077 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____7086 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____7087 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____7086, uu____7087)
                          | FStar_Pervasives_Native.None  ->
                              let uu____7090 = FStar_Syntax_Subst.compress t1 in
                              let uu____7091 = FStar_Syntax_Subst.compress t2 in
                              (uu____7090, uu____7091) in
                        (match uu____7077 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____7113 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____7113 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____7136 =
                                    let uu____7142 =
                                      let uu____7145 =
                                        let uu____7148 =
                                          let uu____7149 =
                                            let uu____7154 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____7154) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____7149 in
                                        FStar_Syntax_Syntax.mk uu____7148 in
                                      uu____7145 FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____7167 =
                                      let uu____7169 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____7169] in
                                    (uu____7142, uu____7167) in
                                  FStar_Pervasives_Native.Some uu____7136
                              | (uu____7178,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____7180)) ->
                                  let uu____7185 =
                                    let uu____7189 =
                                      let uu____7191 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____7191] in
                                    (t11, uu____7189) in
                                  FStar_Pervasives_Native.Some uu____7185
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____7197),uu____7198) ->
                                  let uu____7203 =
                                    let uu____7207 =
                                      let uu____7209 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____7209] in
                                    (t21, uu____7207) in
                                  FStar_Pervasives_Native.Some uu____7203
                              | uu____7214 ->
                                  let uu____7217 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____7217 with
                                   | (head1,uu____7232) ->
                                       let uu____7247 =
                                         let uu____7248 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____7248.FStar_Syntax_Syntax.n in
                                       (match uu____7247 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____7255;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____7257;_}
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
                                        | uu____7263 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7272) ->
                  let uu____7289 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___129_7307  ->
                            match uu___129_7307 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____7312 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____7312 with
                                      | (u',uu____7323) ->
                                          let uu____7338 =
                                            let uu____7339 = whnf env u' in
                                            uu____7339.FStar_Syntax_Syntax.n in
                                          (match uu____7338 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____7343) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____7360 -> false))
                                 | uu____7361 -> false)
                            | uu____7363 -> false)) in
                  (match uu____7289 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____7384 tps =
                         match uu____7384 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7411 =
                                    let uu____7416 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____7416 in
                                  (match uu____7411 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____7435 -> FStar_Pervasives_Native.None) in
                       let uu____7440 =
                         let uu____7445 =
                           let uu____7449 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____7449, []) in
                         make_lower_bound uu____7445 lower_bounds in
                       (match uu____7440 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____7456 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7456
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
                            ((let uu____7469 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7469
                              then
                                let wl' =
                                  let uu___156_7471 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___156_7471.wl_deferred);
                                    ctr = (uu___156_7471.ctr);
                                    defer_ok = (uu___156_7471.defer_ok);
                                    smt_ok = (uu___156_7471.smt_ok);
                                    tcenv = (uu___156_7471.tcenv)
                                  } in
                                let uu____7472 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7472
                              else ());
                             (let uu____7474 =
                                solve_t env eq_prob
                                  (let uu___157_7476 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___157_7476.wl_deferred);
                                     ctr = (uu___157_7476.ctr);
                                     defer_ok = (uu___157_7476.defer_ok);
                                     smt_ok = (uu___157_7476.smt_ok);
                                     tcenv = (uu___157_7476.tcenv)
                                   }) in
                              match uu____7474 with
                              | Success uu____7478 ->
                                  let wl1 =
                                    let uu___158_7480 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___158_7480.wl_deferred);
                                      ctr = (uu___158_7480.ctr);
                                      defer_ok = (uu___158_7480.defer_ok);
                                      smt_ok = (uu___158_7480.smt_ok);
                                      tcenv = (uu___158_7480.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____7482 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____7487 -> FStar_Pervasives_Native.None))))
              | uu____7488 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7495 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____7495
         then
           let uu____7496 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7496
         else ());
        (let uu____7498 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____7498 with
         | (u,args) ->
             let uu____7525 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____7525 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____7556 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____7556 with
                    | (h1,args1) ->
                        let uu____7584 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____7584 with
                         | (h2,uu____7597) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7616 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____7616
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____7631 =
                                          let uu____7633 =
                                            let uu____7634 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____7634 in
                                          [uu____7633] in
                                        FStar_Pervasives_Native.Some
                                          uu____7631))
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
                                       (let uu____7658 =
                                          let uu____7660 =
                                            let uu____7661 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____7661 in
                                          [uu____7660] in
                                        FStar_Pervasives_Native.Some
                                          uu____7658))
                                  else FStar_Pervasives_Native.None
                              | uu____7669 -> FStar_Pervasives_Native.None)) in
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
                             let uu____7735 =
                               let uu____7741 =
                                 let uu____7744 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____7744 in
                               (uu____7741, m1) in
                             FStar_Pervasives_Native.Some uu____7735)
                    | (uu____7753,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7755)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7787),uu____7788) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____7819 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7853) ->
                       let uu____7870 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___130_7888  ->
                                 match uu___130_7888 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____7893 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____7893 with
                                           | (u',uu____7904) ->
                                               let uu____7919 =
                                                 let uu____7920 = whnf env u' in
                                                 uu____7920.FStar_Syntax_Syntax.n in
                                               (match uu____7919 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7924) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____7941 -> false))
                                      | uu____7942 -> false)
                                 | uu____7944 -> false)) in
                       (match uu____7870 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7969 tps =
                              match uu____7969 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____8010 =
                                         let uu____8017 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____8017 in
                                       (match uu____8010 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____8052 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____8059 =
                              let uu____8066 =
                                let uu____8072 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____8072, []) in
                              make_upper_bound uu____8066 upper_bounds in
                            (match uu____8059 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____8081 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____8081
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
                                 ((let uu____8100 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____8100
                                   then
                                     let wl' =
                                       let uu___159_8102 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___159_8102.wl_deferred);
                                         ctr = (uu___159_8102.ctr);
                                         defer_ok = (uu___159_8102.defer_ok);
                                         smt_ok = (uu___159_8102.smt_ok);
                                         tcenv = (uu___159_8102.tcenv)
                                       } in
                                     let uu____8103 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____8103
                                   else ());
                                  (let uu____8105 =
                                     solve_t env eq_prob
                                       (let uu___160_8107 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___160_8107.wl_deferred);
                                          ctr = (uu___160_8107.ctr);
                                          defer_ok = (uu___160_8107.defer_ok);
                                          smt_ok = (uu___160_8107.smt_ok);
                                          tcenv = (uu___160_8107.tcenv)
                                        }) in
                                   match uu____8105 with
                                   | Success uu____8109 ->
                                       let wl1 =
                                         let uu___161_8111 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___161_8111.wl_deferred);
                                           ctr = (uu___161_8111.ctr);
                                           defer_ok =
                                             (uu___161_8111.defer_ok);
                                           smt_ok = (uu___161_8111.smt_ok);
                                           tcenv = (uu___161_8111.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____8113 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____8118 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____8119 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____8180 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____8180
                      then
                        let uu____8181 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____8181
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___162_8213 = hd1 in
                      let uu____8214 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___162_8213.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___162_8213.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____8214
                      } in
                    let hd21 =
                      let uu___163_8218 = hd2 in
                      let uu____8219 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___163_8218.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___163_8218.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____8219
                      } in
                    let prob =
                      let uu____8223 =
                        let uu____8226 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____8226 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____8223 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____8234 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____8234 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____8237 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____8237 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____8255 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____8258 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____8255 uu____8258 in
                         ((let uu____8264 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____8264
                           then
                             let uu____8265 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____8266 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____8265 uu____8266
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____8281 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____8287 = aux scope env [] bs1 bs2 in
              match uu____8287 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____8303 = compress_tprob wl problem in
        solve_t' env uu____8303 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____8336 = head_matches_delta env1 wl1 t1 t2 in
          match uu____8336 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____8353,uu____8354) ->
                   let may_relate head3 =
                     let uu____8369 =
                       let uu____8370 = FStar_Syntax_Util.un_uinst head3 in
                       uu____8370.FStar_Syntax_Syntax.n in
                     match uu____8369 with
                     | FStar_Syntax_Syntax.Tm_name uu____8373 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____8374 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____8390 -> false in
                   let uu____8391 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____8391
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
                                let uu____8408 =
                                  let uu____8409 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____8409 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____8408 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____8411 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____8411
                   else
                     (let uu____8413 =
                        let uu____8414 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____8415 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____8414 uu____8415 in
                      giveup env1 uu____8413 orig)
               | (uu____8416,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___164_8425 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___164_8425.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___164_8425.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___164_8425.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___164_8425.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___164_8425.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___164_8425.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___164_8425.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___164_8425.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____8426,FStar_Pervasives_Native.None ) ->
                   ((let uu____8433 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8433
                     then
                       let uu____8434 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____8435 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____8436 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____8437 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____8434
                         uu____8435 uu____8436 uu____8437
                     else ());
                    (let uu____8439 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____8439 with
                     | (head11,args1) ->
                         let uu____8465 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____8465 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8510 =
                                  let uu____8511 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____8512 = args_to_string args1 in
                                  let uu____8513 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____8514 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8511 uu____8512 uu____8513
                                    uu____8514 in
                                giveup env1 uu____8510 orig
                              else
                                (let uu____8516 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8522 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____8522 = FStar_Syntax_Util.Equal) in
                                 if uu____8516
                                 then
                                   let uu____8523 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____8523 with
                                   | USolved wl2 ->
                                       let uu____8525 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____8525
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8529 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____8529 with
                                    | (base1,refinement1) ->
                                        let uu____8555 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____8555 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____8609 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____8609 with
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
                                                           (fun uu____8626 
                                                              ->
                                                              fun uu____8627 
                                                                ->
                                                                match 
                                                                  (uu____8626,
                                                                    uu____8627)
                                                                with
                                                                | ((a,uu____8637),
                                                                   (a',uu____8639))
                                                                    ->
                                                                    let uu____8644
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
                                                                    uu____8644)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____8650 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8650 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8655 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___165_8689 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___165_8689.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___165_8689.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___165_8689.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___165_8689.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___165_8689.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___165_8689.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___165_8689.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___165_8689.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____8709 = p in
          match uu____8709 with
          | (((u,k),xs,c),ps,(h,uu____8720,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8769 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____8769 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8783 = h gs_xs in
                     let uu____8784 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57) in
                     FStar_Syntax_Util.abs xs1 uu____8783 uu____8784 in
                   ((let uu____8788 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8788
                     then
                       let uu____8789 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____8790 = FStar_Syntax_Print.comp_to_string c in
                       let uu____8791 = FStar_Syntax_Print.term_to_string im in
                       let uu____8792 = FStar_Syntax_Print.tag_of_term im in
                       let uu____8793 =
                         let uu____8794 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____8794
                           (FStar_String.concat ", ") in
                       let uu____8797 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8789 uu____8790 uu____8791 uu____8792
                         uu____8793 uu____8797
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___131_8815 =
          match uu___131_8815 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____8844 = p in
          match uu____8844 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8902 = FStar_List.nth ps i in
              (match uu____8902 with
               | (pi,uu____8905) ->
                   let uu____8910 = FStar_List.nth xs i in
                   (match uu____8910 with
                    | (xi,uu____8917) ->
                        let rec gs k =
                          let uu____8926 = FStar_Syntax_Util.arrow_formals k in
                          match uu____8926 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8978)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8986 = new_uvar r xs k_a in
                                    (match uu____8986 with
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
                                         let uu____9003 = aux subst2 tl1 in
                                         (match uu____9003 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____9018 =
                                                let uu____9020 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____9020 :: gi_xs' in
                                              let uu____9021 =
                                                let uu____9023 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____9023 :: gi_ps' in
                                              (uu____9018, uu____9021))) in
                              aux [] bs in
                        let uu____9026 =
                          let uu____9027 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____9027 in
                        if uu____9026
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____9030 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____9030 with
                           | (g_xs,uu____9037) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____9044 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____9047 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58) in
                                 FStar_Syntax_Util.abs xs uu____9044
                                   uu____9047 in
                               let sub1 =
                                 let uu____9051 =
                                   let uu____9054 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____9059 =
                                     let uu____9062 =
                                       FStar_List.map
                                         (fun uu____9072  ->
                                            match uu____9072 with
                                            | (uu____9077,uu____9078,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____9062 in
                                   mk_problem (p_scope orig) orig uu____9054
                                     (p_rel orig) uu____9059
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____9051 in
                               ((let uu____9088 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____9088
                                 then
                                   let uu____9089 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____9090 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____9089 uu____9090
                                 else ());
                                (let wl2 =
                                   let uu____9093 =
                                     let uu____9095 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____9095 in
                                   solve_prob orig uu____9093
                                     [TERM (u, proj)] wl1 in
                                 let uu____9100 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____9100))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____9124 = lhs in
          match uu____9124 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____9147 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____9147 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____9173 =
                        let uu____9199 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____9199) in
                      FStar_Pervasives_Native.Some uu____9173
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____9282 =
                           let uu____9286 =
                             let uu____9287 = FStar_Syntax_Subst.compress k in
                             uu____9287.FStar_Syntax_Syntax.n in
                           (uu____9286, args) in
                         match uu____9282 with
                         | (uu____9294,[]) ->
                             let uu____9296 =
                               let uu____9302 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____9302) in
                             FStar_Pervasives_Native.Some uu____9296
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____9313,uu____9314) ->
                             let uu____9327 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9327 with
                              | (uv1,uv_args) ->
                                  let uu____9356 =
                                    let uu____9357 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9357.FStar_Syntax_Syntax.n in
                                  (match uu____9356 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9364) ->
                                       let uu____9381 =
                                         pat_vars env [] uv_args in
                                       (match uu____9381 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9397  ->
                                                      let uu____9398 =
                                                        let uu____9399 =
                                                          let uu____9400 =
                                                            let uu____9403 =
                                                              let uu____9404
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9404
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9403 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____9400 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9399 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9398)) in
                                            let c1 =
                                              let uu____9410 =
                                                let uu____9411 =
                                                  let uu____9414 =
                                                    let uu____9415 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9415
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9414 in
                                                FStar_Pervasives_Native.fst
                                                  uu____9411 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9410 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9424 =
                                                let uu____9426 =
                                                  let uu____9427 =
                                                    let uu____9430 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9430
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____9427 in
                                                FStar_Pervasives_Native.Some
                                                  uu____9426 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9424 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____9440 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9443,uu____9444)
                             ->
                             let uu____9456 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9456 with
                              | (uv1,uv_args) ->
                                  let uu____9485 =
                                    let uu____9486 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9486.FStar_Syntax_Syntax.n in
                                  (match uu____9485 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9493) ->
                                       let uu____9510 =
                                         pat_vars env [] uv_args in
                                       (match uu____9510 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9526  ->
                                                      let uu____9527 =
                                                        let uu____9528 =
                                                          let uu____9529 =
                                                            let uu____9532 =
                                                              let uu____9533
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9533
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9532 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____9529 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9528 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9527)) in
                                            let c1 =
                                              let uu____9539 =
                                                let uu____9540 =
                                                  let uu____9543 =
                                                    let uu____9544 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9544
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9543 in
                                                FStar_Pervasives_Native.fst
                                                  uu____9540 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9539 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9553 =
                                                let uu____9555 =
                                                  let uu____9556 =
                                                    let uu____9559 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9559
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____9556 in
                                                FStar_Pervasives_Native.Some
                                                  uu____9555 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9553 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____9569 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9574)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____9606 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____9606
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9630 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____9630 with
                                  | (args1,rest) ->
                                      let uu____9648 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____9648 with
                                       | (xs2,c2) ->
                                           let uu____9656 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____9656
                                             (fun uu____9670  ->
                                                match uu____9670 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9692 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____9692 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____9736 =
                                        let uu____9739 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9739 in
                                      FStar_All.pipe_right uu____9736
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____9747 ->
                             let uu____9751 =
                               let uu____9752 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____9753 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____9754 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9752 uu____9753 uu____9754 in
                             failwith uu____9751 in
                       let uu____9758 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____9758
                         (fun uu____9790  ->
                            match uu____9790 with
                            | (xs1,c1) ->
                                let uu____9818 =
                                  let uu____9841 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9841) in
                                FStar_Pervasives_Native.Some uu____9818)) in
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
                     let uu____9913 = imitate orig env wl1 st in
                     match uu____9913 with
                     | Failed uu____9918 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9924 = project orig env wl1 i st in
                      match uu____9924 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____9931) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____9945 = FStar_Syntax_Util.head_and_args t21 in
                match uu____9945 with
                | (hd1,uu____9956) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9971 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9979 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9980 -> true
                     | uu____9990 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____9993 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____9993
                         then true
                         else
                           ((let uu____9996 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____9996
                             then
                               let uu____9997 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9997
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____10005 =
                    let uu____10008 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____10008
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____10005 FStar_Syntax_Free.names in
                let uu____10039 = FStar_Util.set_is_empty fvs_hd in
                if uu____10039
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____10048 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____10048 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____10056 =
                            let uu____10057 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____10057 in
                          giveup_or_defer1 orig uu____10056
                        else
                          (let uu____10059 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____10059
                           then
                             let uu____10060 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____10060
                              then
                                let uu____10061 = subterms args_lhs in
                                imitate' orig env wl1 uu____10061
                              else
                                ((let uu____10065 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____10065
                                  then
                                    let uu____10066 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____10067 = names_to_string fvs1 in
                                    let uu____10068 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____10066 uu____10067 uu____10068
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____10073 ->
                                        let uu____10074 = sn_binders env vars in
                                        u_abs k_uv uu____10074 t21 in
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
                               (let uu____10083 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____10083
                                then
                                  ((let uu____10085 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____10085
                                    then
                                      let uu____10086 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____10087 = names_to_string fvs1 in
                                      let uu____10088 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____10086 uu____10087 uu____10088
                                    else ());
                                   (let uu____10090 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs)
                                      uu____10090 (- (Prims.parse_int "1"))))
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
                     (let uu____10104 =
                        let uu____10105 = FStar_Syntax_Free.names t1 in
                        check_head uu____10105 t2 in
                      if uu____10104
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____10109 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____10109
                          then
                            let uu____10110 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____10110
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____10113 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____10113 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____10158 =
               match uu____10158 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k in
                   let uu____10189 = FStar_Syntax_Util.arrow_formals k1 in
                   (match uu____10189 with
                    | (all_formals,uu____10200) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____10295  ->
                                        match uu____10295 with
                                        | (x,imp) ->
                                            let uu____10302 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____10302, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____10310 = FStar_Syntax_Util.type_u () in
                                match uu____10310 with
                                | (t1,uu____10314) ->
                                    let uu____10315 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    FStar_Pervasives_Native.fst uu____10315 in
                              let uu____10318 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____10318 with
                               | (t',tm_u1) ->
                                   let uu____10325 = destruct_flex_t t' in
                                   (match uu____10325 with
                                    | (uu____10347,u1,k11,uu____10350) ->
                                        let sol =
                                          let uu____10382 =
                                            let uu____10387 =
                                              u_abs k1 all_formals t' in
                                            ((u, k1), uu____10387) in
                                          TERM uu____10382 in
                                        let t_app =
                                          FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                            pat_args1
                                            FStar_Pervasives_Native.None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10449 = pat_var_opt env pat_args hd1 in
                              (match uu____10449 with
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
                                              (fun uu____10481  ->
                                                 match uu____10481 with
                                                 | (x,uu____10485) ->
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
                                      let uu____10491 =
                                        let uu____10492 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____10492 in
                                      if uu____10491
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10496 =
                                           FStar_Util.set_add
                                             (FStar_Pervasives_Native.fst
                                                formal) pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10496 formals1
                                           tl1)))
                          | uu____10502 -> failwith "Impossible" in
                        let uu____10513 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____10513 all_formals args) in
             let solve_both_pats wl1 uu____10553 uu____10554 r =
               match (uu____10553, uu____10554) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10668 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____10668
                   then
                     let uu____10669 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____10669
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____10684 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____10684
                       then
                         let uu____10685 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____10686 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____10687 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____10688 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____10689 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10685 uu____10686 uu____10687 uu____10688
                           uu____10689
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____10737 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____10737 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10750 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____10750 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10782 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10782 in
                                  let uu____10785 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____10785 k3)
                           else
                             (let uu____10788 =
                                let uu____10789 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____10790 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____10791 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10789 uu____10790 uu____10791 in
                              failwith uu____10788) in
                       let uu____10792 =
                         let uu____10798 =
                           let uu____10806 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____10806 in
                         match uu____10798 with
                         | (bs,k1') ->
                             let uu____10824 =
                               let uu____10832 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____10832 in
                             (match uu____10824 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____10853 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____10853 in
                                  let uu____10858 =
                                    let uu____10861 =
                                      let uu____10862 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____10862.FStar_Syntax_Syntax.n in
                                    let uu____10865 =
                                      let uu____10866 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____10866.FStar_Syntax_Syntax.n in
                                    (uu____10861, uu____10865) in
                                  (match uu____10858 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10874,uu____10875) ->
                                       (k1', [sub_prob])
                                   | (uu____10879,FStar_Syntax_Syntax.Tm_type
                                      uu____10880) -> (k2', [sub_prob])
                                   | uu____10884 ->
                                       let uu____10887 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____10887 with
                                        | (t,uu____10896) ->
                                            let uu____10897 = new_uvar r zs t in
                                            (match uu____10897 with
                                             | (k_zs,uu____10906) ->
                                                 let kprob =
                                                   let uu____10908 =
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
                                                          _0_64) uu____10908 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____10792 with
                       | (k_u',sub_probs) ->
                           let uu____10922 =
                             let uu____10930 =
                               let uu____10931 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____10931 in
                             let uu____10936 =
                               let uu____10939 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____10939 in
                             let uu____10942 =
                               let uu____10945 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____10945 in
                             (uu____10930, uu____10936, uu____10942) in
                           (match uu____10922 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____10964 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____10964 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____10976 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____10976
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____10980 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____10980 with
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
             let solve_one_pat uu____11012 uu____11013 =
               match (uu____11012, uu____11013) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____11077 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____11077
                     then
                       let uu____11078 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____11079 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____11078 uu____11079
                     else ());
                    (let uu____11081 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____11081
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____11095  ->
                              fun uu____11096  ->
                                match (uu____11095, uu____11096) with
                                | ((a,uu____11106),(t21,uu____11108)) ->
                                    let uu____11113 =
                                      let uu____11116 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____11116
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____11113
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2 in
                       let guard =
                         let uu____11120 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____11120 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____11131 = occurs_check env wl (u1, k1) t21 in
                        match uu____11131 with
                        | (occurs_ok,uu____11136) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____11141 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____11141
                            then
                              let sol =
                                let uu____11143 =
                                  let uu____11148 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____11148) in
                                TERM uu____11143 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____11153 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____11153
                               then
                                 let uu____11154 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____11154 with
                                 | (sol,(uu____11164,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____11174 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____11174
                                       then
                                         let uu____11175 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____11175
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____11180 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____11182 = lhs in
             match uu____11182 with
             | (t1,u1,k1,args1) ->
                 let uu____11187 = rhs in
                 (match uu____11187 with
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
                       | uu____11213 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____11219 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____11219 with
                              | (sol,uu____11226) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____11229 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____11229
                                    then
                                      let uu____11230 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____11230
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____11235 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____11237 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____11237
        then
          let uu____11238 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____11238
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____11242 = FStar_Util.physical_equality t1 t2 in
           if uu____11242
           then
             let uu____11243 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____11243
           else
             ((let uu____11246 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____11246
               then
                 let uu____11247 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____11247
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____11250,uu____11251) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____11252,FStar_Syntax_Syntax.Tm_bvar uu____11253) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___132_11293 =
                     match uu___132_11293 with
                     | [] -> c
                     | bs ->
                         let uu____11307 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____11307 in
                   let uu____11317 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____11317 with
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
                                   let uu____11410 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____11410
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____11412 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____11412))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___133_11464 =
                     match uu___133_11464 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____11489 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____11489 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11576 =
                                   let uu____11579 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____11580 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____11579
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11580 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____11576))
               | (FStar_Syntax_Syntax.Tm_abs uu____11583,uu____11584) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11602 -> true
                     | uu____11612 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11640 =
                     let uu____11651 = maybe_eta t1 in
                     let uu____11656 = maybe_eta t2 in
                     (uu____11651, uu____11656) in
                   (match uu____11640 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_11688 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_11688.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_11688.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_11688.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_11688.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_11688.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_11688.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_11688.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_11688.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11707 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11707
                        then
                          let uu____11708 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11708 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11729 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11729
                        then
                          let uu____11730 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11730 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11735 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11746,FStar_Syntax_Syntax.Tm_abs uu____11747) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11765 -> true
                     | uu____11775 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11803 =
                     let uu____11814 = maybe_eta t1 in
                     let uu____11819 = maybe_eta t2 in
                     (uu____11814, uu____11819) in
                   (match uu____11803 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_11851 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_11851.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_11851.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_11851.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_11851.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_11851.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_11851.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_11851.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_11851.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11870 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11870
                        then
                          let uu____11871 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11871 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11892 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11892
                        then
                          let uu____11893 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11893 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11898 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11909,FStar_Syntax_Syntax.Tm_refine uu____11910) ->
                   let uu____11919 = as_refinement env wl t1 in
                   (match uu____11919 with
                    | (x1,phi1) ->
                        let uu____11924 = as_refinement env wl t2 in
                        (match uu____11924 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11930 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____11930 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____11963 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____11963
                                 (guard_on_element wl problem x11) in
                             let fallback uu____11967 =
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
                                 let uu____11973 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____11973 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11980 =
                                   let uu____11983 =
                                     let uu____11984 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____11984 :: (p_scope orig) in
                                   mk_problem uu____11983 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____11980 in
                               let uu____11987 =
                                 solve env1
                                   (let uu___167_11989 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___167_11989.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___167_11989.smt_ok);
                                      tcenv = (uu___167_11989.tcenv)
                                    }) in
                               (match uu____11987 with
                                | Failed uu____11993 -> fallback ()
                                | Success uu____11996 ->
                                    let guard =
                                      let uu____12000 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____12003 =
                                        let uu____12004 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____12004
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____12000
                                        uu____12003 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___168_12011 = wl1 in
                                      {
                                        attempting =
                                          (uu___168_12011.attempting);
                                        wl_deferred =
                                          (uu___168_12011.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___168_12011.defer_ok);
                                        smt_ok = (uu___168_12011.smt_ok);
                                        tcenv = (uu___168_12011.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12013,FStar_Syntax_Syntax.Tm_uvar uu____12014) ->
                   let uu____12035 = destruct_flex_t t1 in
                   let uu____12036 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12035 uu____12036
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12037;
                     FStar_Syntax_Syntax.tk = uu____12038;
                     FStar_Syntax_Syntax.pos = uu____12039;_},uu____12040),FStar_Syntax_Syntax.Tm_uvar
                  uu____12041) ->
                   let uu____12075 = destruct_flex_t t1 in
                   let uu____12076 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12075 uu____12076
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12077,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12078;
                     FStar_Syntax_Syntax.tk = uu____12079;
                     FStar_Syntax_Syntax.pos = uu____12080;_},uu____12081))
                   ->
                   let uu____12115 = destruct_flex_t t1 in
                   let uu____12116 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12115 uu____12116
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12117;
                     FStar_Syntax_Syntax.tk = uu____12118;
                     FStar_Syntax_Syntax.pos = uu____12119;_},uu____12120),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12121;
                     FStar_Syntax_Syntax.tk = uu____12122;
                     FStar_Syntax_Syntax.pos = uu____12123;_},uu____12124))
                   ->
                   let uu____12171 = destruct_flex_t t1 in
                   let uu____12172 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12171 uu____12172
               | (FStar_Syntax_Syntax.Tm_uvar uu____12173,uu____12174) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12185 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____12185 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12189;
                     FStar_Syntax_Syntax.tk = uu____12190;
                     FStar_Syntax_Syntax.pos = uu____12191;_},uu____12192),uu____12193)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12217 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____12217 t2 wl
               | (uu____12221,FStar_Syntax_Syntax.Tm_uvar uu____12222) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____12233,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12234;
                     FStar_Syntax_Syntax.tk = uu____12235;
                     FStar_Syntax_Syntax.pos = uu____12236;_},uu____12237))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12261,FStar_Syntax_Syntax.Tm_type uu____12262) ->
                   solve_t' env
                     (let uu___169_12274 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12274.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12274.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12274.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12274.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12274.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12274.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12274.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12274.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12274.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12275;
                     FStar_Syntax_Syntax.tk = uu____12276;
                     FStar_Syntax_Syntax.pos = uu____12277;_},uu____12278),FStar_Syntax_Syntax.Tm_type
                  uu____12279) ->
                   solve_t' env
                     (let uu___169_12304 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12304.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12304.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12304.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12304.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12304.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12304.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12304.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12304.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12304.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12305,FStar_Syntax_Syntax.Tm_arrow uu____12306) ->
                   solve_t' env
                     (let uu___169_12325 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12325.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12325.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12325.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12325.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12325.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12325.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12325.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12325.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12325.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12326;
                     FStar_Syntax_Syntax.tk = uu____12327;
                     FStar_Syntax_Syntax.pos = uu____12328;_},uu____12329),FStar_Syntax_Syntax.Tm_arrow
                  uu____12330) ->
                   solve_t' env
                     (let uu___169_12362 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12362.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12362.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12362.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12362.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12362.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12362.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12362.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12362.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12362.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____12363,uu____12364) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12377 =
                        let uu____12378 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12378 in
                      if uu____12377
                      then
                        let uu____12379 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___170_12383 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_12383.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_12383.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_12383.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_12383.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_12383.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_12383.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_12383.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_12383.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_12383.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12384 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12379 uu____12384 t2
                          wl
                      else
                        (let uu____12389 = base_and_refinement env wl t2 in
                         match uu____12389 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____12419 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___171_12423 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_12423.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_12423.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_12423.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_12423.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_12423.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_12423.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_12423.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_12423.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_12423.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12424 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12419
                                    uu____12424 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___172_12439 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_12439.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_12439.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12442 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____12442 in
                                  let guard =
                                    let uu____12450 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____12450
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12456;
                     FStar_Syntax_Syntax.tk = uu____12457;
                     FStar_Syntax_Syntax.pos = uu____12458;_},uu____12459),uu____12460)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12486 =
                        let uu____12487 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12487 in
                      if uu____12486
                      then
                        let uu____12488 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___170_12492 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_12492.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_12492.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_12492.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_12492.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_12492.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_12492.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_12492.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_12492.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_12492.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12493 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12488 uu____12493 t2
                          wl
                      else
                        (let uu____12498 = base_and_refinement env wl t2 in
                         match uu____12498 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____12528 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___171_12532 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_12532.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_12532.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_12532.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_12532.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_12532.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_12532.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_12532.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_12532.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_12532.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12533 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12528
                                    uu____12533 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___172_12548 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_12548.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_12548.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12551 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____12551 in
                                  let guard =
                                    let uu____12559 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____12559
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12565,FStar_Syntax_Syntax.Tm_uvar uu____12566) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12578 = base_and_refinement env wl t1 in
                      match uu____12578 with
                      | (t_base,uu____12589) ->
                          solve_t env
                            (let uu___173_12605 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_12605.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_12605.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_12605.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_12605.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_12605.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_12605.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_12605.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_12605.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12608,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12609;
                     FStar_Syntax_Syntax.tk = uu____12610;
                     FStar_Syntax_Syntax.pos = uu____12611;_},uu____12612))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12637 = base_and_refinement env wl t1 in
                      match uu____12637 with
                      | (t_base,uu____12648) ->
                          solve_t env
                            (let uu___173_12664 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_12664.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_12664.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_12664.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_12664.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_12664.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_12664.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_12664.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_12664.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12667,uu____12668) ->
                   let t21 =
                     let uu____12676 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____12676 in
                   solve_t env
                     (let uu___174_12690 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_12690.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___174_12690.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___174_12690.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___174_12690.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_12690.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_12690.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_12690.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_12690.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_12690.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12691,FStar_Syntax_Syntax.Tm_refine uu____12692) ->
                   let t11 =
                     let uu____12700 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____12700 in
                   solve_t env
                     (let uu___175_12714 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_12714.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_12714.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_12714.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_12714.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_12714.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_12714.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_12714.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_12714.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_12714.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12717,uu____12718) ->
                   let head1 =
                     let uu____12736 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12736
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12767 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12767
                       FStar_Pervasives_Native.fst in
                   let uu____12795 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12795
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12804 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12804
                      then
                        let guard =
                          let uu____12811 =
                            let uu____12812 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12812 = FStar_Syntax_Util.Equal in
                          if uu____12811
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12815 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____12815) in
                        let uu____12817 = solve_prob orig guard [] wl in
                        solve env uu____12817
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12820,uu____12821) ->
                   let head1 =
                     let uu____12829 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12829
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12860 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12860
                       FStar_Pervasives_Native.fst in
                   let uu____12888 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12888
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12897 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12897
                      then
                        let guard =
                          let uu____12904 =
                            let uu____12905 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12905 = FStar_Syntax_Util.Equal in
                          if uu____12904
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12908 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____12908) in
                        let uu____12910 = solve_prob orig guard [] wl in
                        solve env uu____12910
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12913,uu____12914) ->
                   let head1 =
                     let uu____12918 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12918
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12949 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12949
                       FStar_Pervasives_Native.fst in
                   let uu____12977 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12977
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12986 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12986
                      then
                        let guard =
                          let uu____12993 =
                            let uu____12994 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12994 = FStar_Syntax_Util.Equal in
                          if uu____12993
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12997 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____12997) in
                        let uu____12999 = solve_prob orig guard [] wl in
                        solve env uu____12999
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____13002,uu____13003) ->
                   let head1 =
                     let uu____13007 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13007
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13038 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13038
                       FStar_Pervasives_Native.fst in
                   let uu____13066 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13066
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13075 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13075
                      then
                        let guard =
                          let uu____13082 =
                            let uu____13083 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13083 = FStar_Syntax_Util.Equal in
                          if uu____13082
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13086 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____13086) in
                        let uu____13088 = solve_prob orig guard [] wl in
                        solve env uu____13088
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____13091,uu____13092) ->
                   let head1 =
                     let uu____13096 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13096
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13127 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13127
                       FStar_Pervasives_Native.fst in
                   let uu____13155 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13155
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13164 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13164
                      then
                        let guard =
                          let uu____13171 =
                            let uu____13172 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13172 = FStar_Syntax_Util.Equal in
                          if uu____13171
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13175 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____13175) in
                        let uu____13177 = solve_prob orig guard [] wl in
                        solve env uu____13177
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____13180,uu____13181) ->
                   let head1 =
                     let uu____13194 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13194
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13225 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13225
                       FStar_Pervasives_Native.fst in
                   let uu____13253 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13253
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13262 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13262
                      then
                        let guard =
                          let uu____13269 =
                            let uu____13270 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13270 = FStar_Syntax_Util.Equal in
                          if uu____13269
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13273 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____13273) in
                        let uu____13275 = solve_prob orig guard [] wl in
                        solve env uu____13275
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13278,FStar_Syntax_Syntax.Tm_match uu____13279) ->
                   let head1 =
                     let uu____13297 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13297
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13328 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13328
                       FStar_Pervasives_Native.fst in
                   let uu____13356 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13356
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13365 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13365
                      then
                        let guard =
                          let uu____13372 =
                            let uu____13373 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13373 = FStar_Syntax_Util.Equal in
                          if uu____13372
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13376 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____13376) in
                        let uu____13378 = solve_prob orig guard [] wl in
                        solve env uu____13378
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13381,FStar_Syntax_Syntax.Tm_uinst uu____13382) ->
                   let head1 =
                     let uu____13390 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13390
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13421 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13421
                       FStar_Pervasives_Native.fst in
                   let uu____13449 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13449
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13458 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13458
                      then
                        let guard =
                          let uu____13465 =
                            let uu____13466 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13466 = FStar_Syntax_Util.Equal in
                          if uu____13465
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13469 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____13469) in
                        let uu____13471 = solve_prob orig guard [] wl in
                        solve env uu____13471
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13474,FStar_Syntax_Syntax.Tm_name uu____13475) ->
                   let head1 =
                     let uu____13479 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13479
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13510 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13510
                       FStar_Pervasives_Native.fst in
                   let uu____13538 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13538
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13547 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13547
                      then
                        let guard =
                          let uu____13554 =
                            let uu____13555 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13555 = FStar_Syntax_Util.Equal in
                          if uu____13554
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13558 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____13558) in
                        let uu____13560 = solve_prob orig guard [] wl in
                        solve env uu____13560
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13563,FStar_Syntax_Syntax.Tm_constant uu____13564) ->
                   let head1 =
                     let uu____13568 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13568
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13599 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13599
                       FStar_Pervasives_Native.fst in
                   let uu____13627 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13627
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13636 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13636
                      then
                        let guard =
                          let uu____13643 =
                            let uu____13644 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13644 = FStar_Syntax_Util.Equal in
                          if uu____13643
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13647 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____13647) in
                        let uu____13649 = solve_prob orig guard [] wl in
                        solve env uu____13649
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13652,FStar_Syntax_Syntax.Tm_fvar uu____13653) ->
                   let head1 =
                     let uu____13657 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13657
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13688 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13688
                       FStar_Pervasives_Native.fst in
                   let uu____13716 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13716
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13725 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13725
                      then
                        let guard =
                          let uu____13732 =
                            let uu____13733 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13733 = FStar_Syntax_Util.Equal in
                          if uu____13732
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13736 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____13736) in
                        let uu____13738 = solve_prob orig guard [] wl in
                        solve env uu____13738
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13741,FStar_Syntax_Syntax.Tm_app uu____13742) ->
                   let head1 =
                     let uu____13755 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13755
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13786 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13786
                       FStar_Pervasives_Native.fst in
                   let uu____13814 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13814
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13823 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13823
                      then
                        let guard =
                          let uu____13830 =
                            let uu____13831 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13831 = FStar_Syntax_Util.Equal in
                          if uu____13830
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13834 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____13834) in
                        let uu____13836 = solve_prob orig guard [] wl in
                        solve env uu____13836
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13840,uu____13841),uu____13842) ->
                   solve_t' env
                     (let uu___176_13872 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_13872.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___176_13872.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___176_13872.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___176_13872.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_13872.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_13872.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_13872.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_13872.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_13872.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13875,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13877,uu____13878)) ->
                   solve_t' env
                     (let uu___177_13908 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___177_13908.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___177_13908.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___177_13908.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___177_13908.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___177_13908.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___177_13908.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___177_13908.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___177_13908.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___177_13908.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13909,uu____13910) ->
                   let uu____13918 =
                     let uu____13919 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13920 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13919
                       uu____13920 in
                   failwith uu____13918
               | (FStar_Syntax_Syntax.Tm_meta uu____13921,uu____13922) ->
                   let uu____13927 =
                     let uu____13928 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13929 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13928
                       uu____13929 in
                   failwith uu____13927
               | (FStar_Syntax_Syntax.Tm_delayed uu____13930,uu____13931) ->
                   let uu____13946 =
                     let uu____13947 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13948 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13947
                       uu____13948 in
                   failwith uu____13946
               | (uu____13949,FStar_Syntax_Syntax.Tm_meta uu____13950) ->
                   let uu____13955 =
                     let uu____13956 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13957 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13956
                       uu____13957 in
                   failwith uu____13955
               | (uu____13958,FStar_Syntax_Syntax.Tm_delayed uu____13959) ->
                   let uu____13974 =
                     let uu____13975 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13976 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13975
                       uu____13976 in
                   failwith uu____13974
               | (uu____13977,FStar_Syntax_Syntax.Tm_let uu____13978) ->
                   let uu____13986 =
                     let uu____13987 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13988 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13987
                       uu____13988 in
                   failwith uu____13986
               | uu____13989 -> giveup env "head tag mismatch" orig)))
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
          (let uu____14021 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____14021
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____14036  ->
                  fun uu____14037  ->
                    match (uu____14036, uu____14037) with
                    | ((a1,uu____14047),(a2,uu____14049)) ->
                        let uu____14054 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_88  -> FStar_TypeChecker_Common.TProb _0_88)
                          uu____14054)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____14060 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p)
                      FStar_Pervasives_Native.fst) sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____14060 in
           let wl1 =
             solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____14081 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____14088)::[] -> wp1
              | uu____14101 ->
                  let uu____14107 =
                    let uu____14108 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____14108 in
                  failwith uu____14107 in
            let uu____14111 =
              let uu____14117 =
                let uu____14118 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____14118 in
              [uu____14117] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____14111;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____14119 = lift_c1 () in solve_eq uu____14119 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___134_14124  ->
                       match uu___134_14124 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____14125 -> false)) in
             let uu____14126 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____14150)::uu____14151,(wp2,uu____14153)::uu____14154)
                   -> (wp1, wp2)
               | uu____14195 ->
                   let uu____14208 =
                     let uu____14209 =
                       let uu____14212 =
                         let uu____14213 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____14214 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____14213 uu____14214 in
                       (uu____14212, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____14209 in
                   raise uu____14208 in
             match uu____14126 with
             | (wpc1,wpc2) ->
                 let uu____14231 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____14231
                 then
                   let uu____14234 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____14234 wl
                 else
                   (let uu____14238 =
                      let uu____14242 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____14242 in
                    match uu____14238 with
                    | (c2_decl,qualifiers) ->
                        let uu____14254 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____14254
                        then
                          let c1_repr =
                            let uu____14257 =
                              let uu____14258 =
                                let uu____14259 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____14259 in
                              let uu____14260 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14258 uu____14260 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14257 in
                          let c2_repr =
                            let uu____14262 =
                              let uu____14263 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____14264 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14263 uu____14264 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14262 in
                          let prob =
                            let uu____14266 =
                              let uu____14269 =
                                let uu____14270 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____14271 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____14270
                                  uu____14271 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____14269 in
                            FStar_TypeChecker_Common.TProb uu____14266 in
                          let wl1 =
                            let uu____14273 =
                              let uu____14275 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____14275 in
                            solve_prob orig uu____14273 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____14282 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____14282
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____14284 =
                                     let uu____14287 =
                                       let uu____14288 =
                                         let uu____14298 =
                                           let uu____14299 =
                                             let uu____14300 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____14300] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____14299 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____14301 =
                                           let uu____14303 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____14304 =
                                             let uu____14306 =
                                               let uu____14307 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____14307 in
                                             [uu____14306] in
                                           uu____14303 :: uu____14304 in
                                         (uu____14298, uu____14301) in
                                       FStar_Syntax_Syntax.Tm_app uu____14288 in
                                     FStar_Syntax_Syntax.mk uu____14287 in
                                   uu____14284
                                     (FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____14318 =
                                    let uu____14321 =
                                      let uu____14322 =
                                        let uu____14332 =
                                          let uu____14333 =
                                            let uu____14334 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____14334] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____14333 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____14335 =
                                          let uu____14337 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____14338 =
                                            let uu____14340 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____14341 =
                                              let uu____14343 =
                                                let uu____14344 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14344 in
                                              [uu____14343] in
                                            uu____14340 :: uu____14341 in
                                          uu____14337 :: uu____14338 in
                                        (uu____14332, uu____14335) in
                                      FStar_Syntax_Syntax.Tm_app uu____14322 in
                                    FStar_Syntax_Syntax.mk uu____14321 in
                                  uu____14318
                                    (FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____14355 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____14355 in
                           let wl1 =
                             let uu____14361 =
                               let uu____14363 =
                                 let uu____14366 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____14366 g in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____14363 in
                             solve_prob orig uu____14361 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____14376 = FStar_Util.physical_equality c1 c2 in
        if uu____14376
        then
          let uu____14377 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____14377
        else
          ((let uu____14380 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____14380
            then
              let uu____14381 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____14382 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14381
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14382
            else ());
           (let uu____14384 =
              let uu____14387 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____14388 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____14387, uu____14388) in
            match uu____14384 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14392),FStar_Syntax_Syntax.Total
                    (t2,uu____14394)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14407 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____14407 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14410,FStar_Syntax_Syntax.Total uu____14411) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14423),FStar_Syntax_Syntax.Total
                    (t2,uu____14425)) ->
                     let uu____14438 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____14438 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14442),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14444)) ->
                     let uu____14457 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____14457 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14461),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14463)) ->
                     let uu____14476 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____14476 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14479,FStar_Syntax_Syntax.Comp uu____14480) ->
                     let uu____14486 =
                       let uu___178_14489 = problem in
                       let uu____14492 =
                         let uu____14493 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14493 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14489.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14492;
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14489.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___178_14489.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___178_14489.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14489.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14489.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14489.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14489.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14489.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14486 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14494,FStar_Syntax_Syntax.Comp uu____14495) ->
                     let uu____14501 =
                       let uu___178_14504 = problem in
                       let uu____14507 =
                         let uu____14508 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14508 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14504.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14507;
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14504.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___178_14504.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___178_14504.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14504.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14504.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14504.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14504.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14504.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14501 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14509,FStar_Syntax_Syntax.GTotal uu____14510) ->
                     let uu____14516 =
                       let uu___179_14519 = problem in
                       let uu____14522 =
                         let uu____14523 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14523 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_14519.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___179_14519.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___179_14519.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14522;
                         FStar_TypeChecker_Common.element =
                           (uu___179_14519.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_14519.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_14519.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_14519.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_14519.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_14519.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14516 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14524,FStar_Syntax_Syntax.Total uu____14525) ->
                     let uu____14531 =
                       let uu___179_14534 = problem in
                       let uu____14537 =
                         let uu____14538 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14538 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_14534.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___179_14534.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___179_14534.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14537;
                         FStar_TypeChecker_Common.element =
                           (uu___179_14534.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_14534.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_14534.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_14534.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_14534.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_14534.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14531 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14539,FStar_Syntax_Syntax.Comp uu____14540) ->
                     let uu____14541 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____14541
                     then
                       let uu____14542 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____14542 wl
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
                           (let uu____14552 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____14552
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14554 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____14554 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____14556 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14558 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____14558) in
                                if uu____14556
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
                                  (let uu____14561 =
                                     let uu____14562 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____14563 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14562 uu____14563 in
                                   giveup env uu____14561 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14569 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14592  ->
              match uu____14592 with
              | (uu____14599,uu____14600,u,uu____14602,uu____14603,uu____14604)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____14569 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14623 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____14623 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____14633 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____14650  ->
                match uu____14650 with
                | (u1,u2) ->
                    let uu____14655 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____14656 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____14655 uu____14656)) in
      FStar_All.pipe_right uu____14633 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14670,[])) -> "{}"
      | uu____14683 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14693 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____14693
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____14696 =
              FStar_List.map
                (fun uu____14703  ->
                   match uu____14703 with
                   | (uu____14706,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____14696 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____14710 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14710 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14755 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____14755
    then
      let uu____14756 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____14757 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14756
        (rel_to_string rel) uu____14757
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
            let uu____14781 =
              let uu____14783 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____14783 in
            FStar_Syntax_Syntax.new_bv uu____14781 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____14789 =
              let uu____14791 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____14791 in
            let uu____14793 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____14789 uu____14793 in
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
          let uu____14819 = FStar_Options.eager_inference () in
          if uu____14819
          then
            let uu___180_14820 = probs in
            {
              attempting = (uu___180_14820.attempting);
              wl_deferred = (uu___180_14820.wl_deferred);
              ctr = (uu___180_14820.ctr);
              defer_ok = false;
              smt_ok = (uu___180_14820.smt_ok);
              tcenv = (uu___180_14820.tcenv)
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
             (let uu____14831 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____14831
              then
                let uu____14832 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____14832
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
          ((let uu____14844 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____14844
            then
              let uu____14845 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14845
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f in
            (let uu____14849 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____14849
             then
               let uu____14850 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14850
             else ());
            (let f2 =
               let uu____14853 =
                 let uu____14854 = FStar_Syntax_Util.unmeta f1 in
                 uu____14854.FStar_Syntax_Syntax.n in
               match uu____14853 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14858 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___181_14859 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___181_14859.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_14859.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_14859.FStar_TypeChecker_Env.implicits)
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
            let uu____14877 =
              let uu____14878 =
                let uu____14879 =
                  let uu____14880 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____14880
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14879;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____14878 in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____14877
let with_guard_no_simp env prob dopt =
  match dopt with
  | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some d ->
      let uu____14917 =
        let uu____14918 =
          let uu____14919 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst in
          FStar_All.pipe_right uu____14919
            (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
        {
          FStar_TypeChecker_Env.guard_f = uu____14918;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      FStar_Pervasives_Native.Some uu____14917
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
          (let uu____14949 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14949
           then
             let uu____14950 = FStar_Syntax_Print.term_to_string t1 in
             let uu____14951 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14950
               uu____14951
           else ());
          (let prob =
             let uu____14954 =
               let uu____14957 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____14957 in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____14954 in
           let g =
             let uu____14962 =
               let uu____14964 = singleton' env prob smt_ok in
               solve_and_commit env uu____14964
                 (fun uu____14966  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____14962 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14983 = try_teq true env t1 t2 in
        match uu____14983 with
        | FStar_Pervasives_Native.None  ->
            let uu____14985 =
              let uu____14986 =
                let uu____14989 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____14990 = FStar_TypeChecker_Env.get_range env in
                (uu____14989, uu____14990) in
              FStar_Errors.Error uu____14986 in
            raise uu____14985
        | FStar_Pervasives_Native.Some g ->
            ((let uu____14993 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____14993
              then
                let uu____14994 = FStar_Syntax_Print.term_to_string t1 in
                let uu____14995 = FStar_Syntax_Print.term_to_string t2 in
                let uu____14996 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14994
                  uu____14995 uu____14996
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
          (let uu____15016 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____15016
           then
             let uu____15017 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____15018 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____15017
               uu____15018
           else ());
          (let uu____15020 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____15020 with
           | (prob,x) ->
               let g =
                 let uu____15028 =
                   let uu____15030 = singleton' env prob smt_ok in
                   solve_and_commit env uu____15030
                     (fun uu____15032  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____15028 in
               ((let uu____15038 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____15038
                 then
                   let uu____15039 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____15040 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____15041 =
                     let uu____15042 = FStar_Util.must g in
                     guard_to_string env uu____15042 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____15039 uu____15040 uu____15041
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
          let uu____15073 = FStar_TypeChecker_Env.get_range env in
          let uu____15074 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____15073 uu____15074
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____15089 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____15089
         then
           let uu____15090 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____15091 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____15090
             uu____15091
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____15096 =
             let uu____15099 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____15099 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____15096 in
         let uu____15102 =
           let uu____15104 = singleton env prob in
           solve_and_commit env uu____15104
             (fun uu____15106  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____15102)
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
      fun uu____15128  ->
        match uu____15128 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____15153 =
                 let uu____15154 =
                   let uu____15157 =
                     let uu____15158 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____15159 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____15158 uu____15159 in
                   let uu____15160 = FStar_TypeChecker_Env.get_range env in
                   (uu____15157, uu____15160) in
                 FStar_Errors.Error uu____15154 in
               raise uu____15153) in
            let equiv1 v1 v' =
              let uu____15168 =
                let uu____15171 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____15172 = FStar_Syntax_Subst.compress_univ v' in
                (uu____15171, uu____15172) in
              match uu____15168 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____15183 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____15202 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____15202 with
                      | FStar_Syntax_Syntax.U_unif uu____15206 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____15224  ->
                                    match uu____15224 with
                                    | (u,v') ->
                                        let uu____15230 = equiv1 v1 v' in
                                        if uu____15230
                                        then
                                          let uu____15232 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____15232 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____15242 -> [])) in
            let uu____15245 =
              let wl =
                let uu___182_15248 = empty_worklist env in
                {
                  attempting = (uu___182_15248.attempting);
                  wl_deferred = (uu___182_15248.wl_deferred);
                  ctr = (uu___182_15248.ctr);
                  defer_ok = false;
                  smt_ok = (uu___182_15248.smt_ok);
                  tcenv = (uu___182_15248.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____15260  ->
                      match uu____15260 with
                      | (lb,v1) ->
                          let uu____15265 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____15265 with
                           | USolved wl1 -> ()
                           | uu____15267 -> fail lb v1))) in
            let rec check_ineq uu____15273 =
              match uu____15273 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____15280) -> true
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
                      uu____15295,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____15297,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____15304) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____15309,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____15315 -> false) in
            let uu____15318 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____15328  ->
                      match uu____15328 with
                      | (u,v1) ->
                          let uu____15333 = check_ineq (u, v1) in
                          if uu____15333
                          then true
                          else
                            ((let uu____15336 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____15336
                              then
                                let uu____15337 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____15338 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____15337
                                  uu____15338
                              else ());
                             false))) in
            if uu____15318
            then ()
            else
              ((let uu____15342 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____15342
                then
                  ((let uu____15344 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____15344);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____15350 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____15350))
                else ());
               (let uu____15356 =
                  let uu____15357 =
                    let uu____15360 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____15360) in
                  FStar_Errors.Error uu____15357 in
                raise uu____15356))
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
      let fail uu____15397 =
        match uu____15397 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____15407 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____15407
       then
         let uu____15408 = wl_to_string wl in
         let uu____15409 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____15408 uu____15409
       else ());
      (let g1 =
         let uu____15424 = solve_and_commit env wl fail in
         match uu____15424 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___183_15431 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___183_15431.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___183_15431.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___183_15431.FStar_TypeChecker_Env.implicits)
             }
         | uu____15434 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___184_15437 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___184_15437.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___184_15437.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___184_15437.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____15450 = FStar_ST.read last_proof_ns in
    match uu____15450 with
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
            let uu___185_15491 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___185_15491.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___185_15491.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___185_15491.FStar_TypeChecker_Env.implicits)
            } in
          let uu____15492 =
            let uu____15493 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____15493 in
          if uu____15492
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15499 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____15499
                   then
                     let uu____15500 = FStar_TypeChecker_Env.get_range env in
                     let uu____15501 =
                       let uu____15502 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15502 in
                     FStar_Errors.diag uu____15500 uu____15501
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   let uu____15505 = check_trivial vc1 in
                   match uu____15505 with
                   | FStar_TypeChecker_Common.Trivial  ->
                       FStar_Pervasives_Native.Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then
                         ((let uu____15510 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15510
                           then
                             let uu____15511 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____15512 =
                               let uu____15513 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1
                                 "Cannot solve without SMT : %s\n"
                                 uu____15513 in
                             FStar_Errors.diag uu____15511 uu____15512
                           else ());
                          FStar_Pervasives_Native.None)
                       else
                         ((let uu____15518 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15518
                           then
                             let uu____15519 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____15520 =
                               let uu____15521 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15521 in
                             FStar_Errors.diag uu____15519 uu____15520
                           else ());
                          (let vcs =
                             let uu____15528 = FStar_Options.use_tactics () in
                             if uu____15528
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else
                               (let uu____15534 =
                                  let uu____15538 = FStar_Options.peek () in
                                  (env, vc2, uu____15538) in
                                [uu____15534]) in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____15559  ->
                                   match uu____15559 with
                                   | (env1,goal,opts) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify;
                                           FStar_TypeChecker_Normalize.Primops]
                                           env1 goal in
                                       let uu____15567 = check_trivial goal1 in
                                       (match uu____15567 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____15569 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____15569
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            (FStar_Options.push ();
                                             FStar_Options.set opts;
                                             maybe_update_proof_ns env1;
                                             (let uu____15576 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____15576
                                              then
                                                let uu____15577 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____15578 =
                                                  let uu____15579 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____15580 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____15579 uu____15580 in
                                                FStar_Errors.diag uu____15577
                                                  uu____15578
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
      let uu____15592 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____15592 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____15597 =
            let uu____15598 =
              let uu____15601 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____15601) in
            FStar_Errors.Error uu____15598 in
          raise uu____15597
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15610 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____15610 with
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
        let uu____15627 = FStar_Syntax_Unionfind.find u in
        match uu____15627 with
        | FStar_Pervasives_Native.None  -> true
        | uu____15629 -> false in
      let rec until_fixpoint acc implicits =
        let uu____15642 = acc in
        match uu____15642 with
        | (out,changed) ->
            (match implicits with
             | [] ->
                 if Prims.op_Negation changed
                 then out
                 else until_fixpoint ([], false) out
             | hd1::tl1 ->
                 let uu____15688 = hd1 in
                 (match uu____15688 with
                  | (uu____15695,env,u,tm,k,r) ->
                      let uu____15701 = unresolved u in
                      if uu____15701
                      then until_fixpoint ((hd1 :: out), changed) tl1
                      else
                        (let env1 =
                           FStar_TypeChecker_Env.set_expected_typ env k in
                         let tm1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta] env1 tm in
                         (let uu____15719 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "RelCheck") in
                          if uu____15719
                          then
                            let uu____15720 =
                              FStar_Syntax_Print.uvar_to_string u in
                            let uu____15721 =
                              FStar_Syntax_Print.term_to_string tm1 in
                            let uu____15722 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print3
                              "Checking uvar %s resolved to %s at type %s\n"
                              uu____15720 uu____15721 uu____15722
                          else ());
                         (let env2 =
                            if forcelax
                            then
                              let uu___186_15725 = env1 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___186_15725.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___186_15725.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___186_15725.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___186_15725.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___186_15725.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___186_15725.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___186_15725.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___186_15725.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___186_15725.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___186_15725.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___186_15725.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___186_15725.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___186_15725.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___186_15725.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___186_15725.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___186_15725.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___186_15725.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___186_15725.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___186_15725.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___186_15725.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___186_15725.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___186_15725.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___186_15725.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___186_15725.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___186_15725.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___186_15725.FStar_TypeChecker_Env.is_native_tactic)
                              }
                            else env1 in
                          let uu____15727 =
                            env2.FStar_TypeChecker_Env.type_of
                              (let uu___187_15732 = env2 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___187_15732.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___187_15732.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___187_15732.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___187_15732.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___187_15732.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___187_15732.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___187_15732.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___187_15732.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___187_15732.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___187_15732.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___187_15732.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___187_15732.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___187_15732.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___187_15732.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___187_15732.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___187_15732.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___187_15732.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___187_15732.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___187_15732.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___187_15732.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___187_15732.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___187_15732.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___187_15732.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___187_15732.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___187_15732.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___187_15732.FStar_TypeChecker_Env.is_native_tactic)
                               }) tm1 in
                          match uu____15727 with
                          | (uu____15733,uu____15734,g1) ->
                              let g2 =
                                if env2.FStar_TypeChecker_Env.is_pattern
                                then
                                  let uu___188_15737 = g1 in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      FStar_TypeChecker_Common.Trivial;
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___188_15737.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___188_15737.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits =
                                      (uu___188_15737.FStar_TypeChecker_Env.implicits)
                                  }
                                else g1 in
                              let g' =
                                let uu____15740 =
                                  discharge_guard'
                                    (FStar_Pervasives_Native.Some
                                       (fun uu____15745  ->
                                          FStar_Syntax_Print.term_to_string
                                            tm1)) env2 g2 true in
                                match uu____15740 with
                                | FStar_Pervasives_Native.Some g3 -> g3
                                | FStar_Pervasives_Native.None  ->
                                    failwith
                                      "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                              until_fixpoint
                                ((FStar_List.append
                                    g'.FStar_TypeChecker_Env.implicits out),
                                  true) tl1)))) in
      let uu___189_15760 = g in
      let uu____15761 =
        until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___189_15760.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___189_15760.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs =
          (uu___189_15760.FStar_TypeChecker_Env.univ_ineqs);
        FStar_TypeChecker_Env.implicits = uu____15761
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
        let uu____15799 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____15799 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15806 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15806
      | (reason,uu____15808,uu____15809,e,t,r)::uu____15813 ->
          let uu____15827 =
            let uu____15828 =
              let uu____15831 =
                let uu____15832 = FStar_Syntax_Print.term_to_string t in
                let uu____15833 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____15832 uu____15833 in
              (uu____15831, r) in
            FStar_Errors.Error uu____15828 in
          raise uu____15827
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___190_15842 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___190_15842.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___190_15842.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___190_15842.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15863 = try_teq false env t1 t2 in
        match uu____15863 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____15866 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____15866 with
             | FStar_Pervasives_Native.Some uu____15870 -> true
             | FStar_Pervasives_Native.None  -> false)