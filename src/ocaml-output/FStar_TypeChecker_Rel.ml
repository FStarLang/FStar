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
  fun uu___107_664  ->
    match uu___107_664 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____680 =
    let uu____681 = FStar_Syntax_Subst.compress t in
    uu____681.FStar_Syntax_Syntax.n in
  match uu____680 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____702 = FStar_Syntax_Print.uvar_to_string u in
      let uu____703 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____702 uu____703
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____706;
         FStar_Syntax_Syntax.pos = uu____707;
         FStar_Syntax_Syntax.vars = uu____708;_},args)
      ->
      let uu____740 = FStar_Syntax_Print.uvar_to_string u in
      let uu____741 = FStar_Syntax_Print.term_to_string ty in
      let uu____742 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" uu____740 uu____741 uu____742
  | uu____743 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___108_751  ->
      match uu___108_751 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____755 =
            let uu____757 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____758 =
              let uu____760 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____761 =
                let uu____763 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____764 =
                  let uu____766 =
                    let uu____768 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____769 =
                      let uu____771 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____772 =
                        let uu____774 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (FStar_Pervasives_Native.fst
                               p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____775 =
                          let uu____777 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____777] in
                        uu____774 :: uu____775 in
                      uu____771 :: uu____772 in
                    uu____768 :: uu____769 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____766 in
                uu____763 :: uu____764 in
              uu____760 :: uu____761 in
            uu____757 :: uu____758 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____755
      | FStar_TypeChecker_Common.CProb p ->
          let uu____782 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____783 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____782
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____783
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___109_791  ->
      match uu___109_791 with
      | UNIV (u,t) ->
          let x =
            let uu____795 = FStar_Options.hide_uvar_nums () in
            if uu____795
            then "?"
            else
              (let uu____797 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____797 FStar_Util.string_of_int) in
          let uu____798 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____798
      | TERM ((u,uu____800),t) ->
          let x =
            let uu____805 = FStar_Options.hide_uvar_nums () in
            if uu____805
            then "?"
            else
              (let uu____807 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____807 FStar_Util.string_of_int) in
          let uu____808 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____808
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____819 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____819 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____828 =
      let uu____830 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____830
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____828 (FStar_String.concat ", ")
let args_to_string args =
  let uu____850 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____861  ->
            match uu____861 with
            | (x,uu____865) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right uu____850 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____871 =
      let uu____872 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____872 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____871;
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
        let uu___140_888 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___140_888.wl_deferred);
          ctr = (uu___140_888.ctr);
          defer_ok = (uu___140_888.defer_ok);
          smt_ok;
          tcenv = (uu___140_888.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___141_918 = empty_worklist env in
  let uu____919 = FStar_List.map FStar_Pervasives_Native.snd g in
  {
    attempting = uu____919;
    wl_deferred = (uu___141_918.wl_deferred);
    ctr = (uu___141_918.ctr);
    defer_ok = false;
    smt_ok = (uu___141_918.smt_ok);
    tcenv = (uu___141_918.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___142_934 = wl in
        {
          attempting = (uu___142_934.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___142_934.ctr);
          defer_ok = (uu___142_934.defer_ok);
          smt_ok = (uu___142_934.smt_ok);
          tcenv = (uu___142_934.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___143_948 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___143_948.wl_deferred);
        ctr = (uu___143_948.ctr);
        defer_ok = (uu___143_948.defer_ok);
        smt_ok = (uu___143_948.smt_ok);
        tcenv = (uu___143_948.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____962 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____962
         then
           let uu____963 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____963
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___110_968  ->
    match uu___110_968 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___144_987 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___144_987.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___144_987.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___144_987.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___144_987.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___144_987.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___144_987.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___144_987.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___111_1012  ->
    match uu___111_1012 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___112_1030  ->
      match uu___112_1030 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___113_1034  ->
    match uu___113_1034 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___114_1044  ->
    match uu___114_1044 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___115_1055  ->
    match uu___115_1055 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___116_1066  ->
    match uu___116_1066 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___117_1078  ->
    match uu___117_1078 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___118_1090  ->
    match uu___118_1090 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___119_1100  ->
    match uu___119_1100 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____1115 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1115 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1131  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1190 = next_pid () in
  let uu____1191 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1190;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1191;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1247 = next_pid () in
  let uu____1248 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1247;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1248;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1297 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1297;
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
        let uu____1357 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1357
        then
          let uu____1358 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1359 = prob_to_string env d in
          let uu____1360 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1358 uu____1359 uu____1360 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1365 -> failwith "impossible" in
           let uu____1366 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1374 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1375 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1374, uu____1375)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1379 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1380 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1379, uu____1380) in
           match uu____1366 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___120_1394  ->
            match uu___120_1394 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1402 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1404),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___121_1421  ->
           match uu___121_1421 with
           | UNIV uu____1423 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1427),t) ->
               let uu____1431 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1431
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
        (fun uu___122_1449  ->
           match uu___122_1449 with
           | UNIV (u',t) ->
               let uu____1453 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1453
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1456 -> FStar_Pervasives_Native.None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1465 =
        let uu____1466 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1466 in
      FStar_Syntax_Subst.compress uu____1465
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1475 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1475
let norm_arg env t =
  let uu____1497 = sn env (FStar_Pervasives_Native.fst t) in
  (uu____1497, (FStar_Pervasives_Native.snd t))
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
           (fun uu____1520  ->
              match uu____1520 with
              | (x,imp) ->
                  let uu____1527 =
                    let uu___145_1528 = x in
                    let uu____1529 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___145_1528.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___145_1528.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1529
                    } in
                  (uu____1527, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1546 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1546
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1549 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1549
        | uu____1551 -> u2 in
      let uu____1552 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1552
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
          (let uu____1668 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____1668 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1680;
               FStar_Syntax_Syntax.pos = uu____1681;
               FStar_Syntax_Syntax.vars = uu____1682;_} ->
               ((x1.FStar_Syntax_Syntax.sort),
                 (FStar_Pervasives_Native.Some (x1, phi1)))
           | tt ->
               let uu____1703 =
                 let uu____1704 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1705 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1704
                   uu____1705 in
               failwith uu____1703)
    | FStar_Syntax_Syntax.Tm_uinst uu____1715 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1742 =
             let uu____1743 = FStar_Syntax_Subst.compress t1' in
             uu____1743.FStar_Syntax_Syntax.n in
           match uu____1742 with
           | FStar_Syntax_Syntax.Tm_refine uu____1755 -> aux true t1'
           | uu____1760 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1772 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1795 =
             let uu____1796 = FStar_Syntax_Subst.compress t1' in
             uu____1796.FStar_Syntax_Syntax.n in
           match uu____1795 with
           | FStar_Syntax_Syntax.Tm_refine uu____1808 -> aux true t1'
           | uu____1813 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_app uu____1825 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1857 =
             let uu____1858 = FStar_Syntax_Subst.compress t1' in
             uu____1858.FStar_Syntax_Syntax.n in
           match uu____1857 with
           | FStar_Syntax_Syntax.Tm_refine uu____1870 -> aux true t1'
           | uu____1875 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_type uu____1887 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_constant uu____1899 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_name uu____1911 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1923 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1935 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_abs uu____1954 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1975 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_let uu____1997 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_match uu____2016 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_meta uu____2042 ->
        let uu____2047 =
          let uu____2048 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2049 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2048
            uu____2049 in
        failwith uu____2047
    | FStar_Syntax_Syntax.Tm_ascribed uu____2059 ->
        let uu____2077 =
          let uu____2078 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2079 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2078
            uu____2079 in
        failwith uu____2077
    | FStar_Syntax_Syntax.Tm_delayed uu____2089 ->
        let uu____2104 =
          let uu____2105 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2106 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2105
            uu____2106 in
        failwith uu____2104
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____2116 =
          let uu____2117 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2118 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2117
            uu____2118 in
        failwith uu____2116 in
  let uu____2128 = whnf env t1 in aux false uu____2128
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____2139 =
        let uu____2149 = empty_worklist env in
        base_and_refinement env uu____2149 t in
      FStar_All.pipe_right uu____2139 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2174 = FStar_Syntax_Syntax.null_bv t in
    (uu____2174, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____2198 = base_and_refinement env wl t in
  match uu____2198 with
  | (t_base,refinement) ->
      (match refinement with
       | FStar_Pervasives_Native.None  -> trivial_refinement t_base
       | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
let force_refinement uu____2259 =
  match uu____2259 with
  | (t_base,refopt) ->
      let uu____2273 =
        match refopt with
        | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
        | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
      (match uu____2273 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___123_2299  ->
      match uu___123_2299 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2303 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2304 =
            let uu____2305 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____2305 in
          let uu____2306 =
            let uu____2307 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____2307 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2303 uu____2304
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2306
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2311 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2312 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____2313 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2311 uu____2312
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2313
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2318 =
      let uu____2320 =
        let uu____2322 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2336  ->
                  match uu____2336 with | (uu____2340,uu____2341,x) -> x)) in
        FStar_List.append wl.attempting uu____2322 in
      FStar_List.map (wl_prob_to_string wl) uu____2320 in
    FStar_All.pipe_right uu____2318 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2362 =
          let uu____2372 =
            let uu____2373 = FStar_Syntax_Subst.compress k in
            uu____2373.FStar_Syntax_Syntax.n in
          match uu____2372 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2418 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2418)
              else
                (let uu____2432 = FStar_Syntax_Util.abs_formals t in
                 match uu____2432 with
                 | (ys',t1,uu____2448) ->
                     let uu____2451 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2451))
          | uu____2472 ->
              let uu____2473 =
                let uu____2479 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____2479) in
              ((ys, t), uu____2473) in
        match uu____2362 with
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
                 let uu____2531 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2531 c in
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
            let uu____2559 = p_guard prob in
            match uu____2559 with
            | (uu____2562,uv) ->
                ((let uu____2565 =
                    let uu____2566 = FStar_Syntax_Subst.compress uv in
                    uu____2566.FStar_Syntax_Syntax.n in
                  match uu____2565 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2590 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2590
                        then
                          let uu____2591 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2592 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2593 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2591
                            uu____2592 uu____2593
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2595 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___146_2598 = wl in
                  {
                    attempting = (uu___146_2598.attempting);
                    wl_deferred = (uu___146_2598.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___146_2598.defer_ok);
                    smt_ok = (uu___146_2598.smt_ok);
                    tcenv = (uu___146_2598.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2614 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2614
         then
           let uu____2615 = FStar_Util.string_of_int pid in
           let uu____2616 =
             let uu____2617 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2617 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2615 uu____2616
         else ());
        commit sol;
        (let uu___147_2622 = wl in
         {
           attempting = (uu___147_2622.attempting);
           wl_deferred = (uu___147_2622.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___147_2622.defer_ok);
           smt_ok = (uu___147_2622.smt_ok);
           tcenv = (uu___147_2622.tcenv)
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
            | (uu____2655,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2663 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____2663 in
          (let uu____2669 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2669
           then
             let uu____2670 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2671 =
               let uu____2672 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2672 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2670 uu____2671
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2701 =
    let uu____2705 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2705 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2701
    (FStar_Util.for_some
       (fun uu____2725  ->
          match uu____2725 with
          | (uv,uu____2729) ->
              FStar_Syntax_Unionfind.equiv uv
                (FStar_Pervasives_Native.fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2768 = occurs wl uk t in Prims.op_Negation uu____2768 in
  let msg =
    if occurs_ok
    then FStar_Pervasives_Native.None
    else
      (let uu____2773 =
         let uu____2774 =
           FStar_Syntax_Print.uvar_to_string (FStar_Pervasives_Native.fst uk) in
         let uu____2775 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2774 uu____2775 in
       FStar_Pervasives_Native.Some uu____2773) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2830 = occurs_check env wl uk t in
  match uu____2830 with
  | (occurs_ok,msg) ->
      let uu____2847 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2847, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  ->
            fun x  -> FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2917 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2948  ->
            fun uu____2949  ->
              match (uu____2948, uu____2949) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2992 =
                    let uu____2993 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2993 in
                  if uu____2992
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____3007 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____3007
                     then
                       let uu____3014 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____3014)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2917 with | (isect,uu____3036) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____3099  ->
          fun uu____3100  ->
            match (uu____3099, uu____3100) with
            | ((a,uu____3110),(b,uu____3112)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____3161 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____3170  ->
                match uu____3170 with
                | (b,uu____3174) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____3161
      then FStar_Pervasives_Native.None
      else
        FStar_Pervasives_Native.Some (a, (FStar_Pervasives_Native.snd hd1))
  | uu____3183 -> FStar_Pervasives_Native.None
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
            let uu____3228 = pat_var_opt env seen hd1 in
            (match uu____3228 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____3236 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____3236
                   then
                     let uu____3237 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____3237
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3250 =
      let uu____3251 = FStar_Syntax_Subst.compress t in
      uu____3251.FStar_Syntax_Syntax.n in
    match uu____3250 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3254 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3265;
           FStar_Syntax_Syntax.tk = uu____3266;
           FStar_Syntax_Syntax.pos = uu____3267;
           FStar_Syntax_Syntax.vars = uu____3268;_},uu____3269)
        -> true
    | uu____3294 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3366;
         FStar_Syntax_Syntax.pos = uu____3367;
         FStar_Syntax_Syntax.vars = uu____3368;_},args)
      -> (t, uv, k, args)
  | uu____3415 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____3476 = destruct_flex_t t in
  match uu____3476 with
  | (t1,uv,k,args) ->
      let uu____3552 = pat_vars env [] args in
      (match uu____3552 with
       | FStar_Pervasives_Native.Some vars ->
           ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
       | uu____3614 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3668 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3693 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3698 -> false
let head_match: match_result -> match_result =
  fun uu___124_3702  ->
    match uu___124_3702 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3711 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3722 ->
          let uu____3723 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3723 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____3729 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____3745 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3751 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____3767 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____3768 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____3769 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____3780 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____3788 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3804) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3810,uu____3811) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3841) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3856;
             FStar_Syntax_Syntax.index = uu____3857;
             FStar_Syntax_Syntax.sort = t2;_},uu____3859)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3866 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3867 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3868 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3876 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3887 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____3887
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
            let uu____3909 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3909
            then FullMatch
            else
              (let uu____3911 =
                 let uu____3916 =
                   let uu____3918 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____3918 in
                 let uu____3919 =
                   let uu____3921 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____3921 in
                 (uu____3916, uu____3919) in
               MisMatch uu____3911)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3925),FStar_Syntax_Syntax.Tm_uinst (g,uu____3927)) ->
            let uu____3936 = head_matches env f g in
            FStar_All.pipe_right uu____3936 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3943),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3945)) ->
            let uu____3978 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____3978
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3983),FStar_Syntax_Syntax.Tm_refine (y,uu____3985)) ->
            let uu____3994 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3994 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3996),uu____3997) ->
            let uu____4002 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____4002 head_match
        | (uu____4003,FStar_Syntax_Syntax.Tm_refine (x,uu____4005)) ->
            let uu____4010 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____4010 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____4011,FStar_Syntax_Syntax.Tm_type
           uu____4012) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____4013,FStar_Syntax_Syntax.Tm_arrow uu____4014) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____4030),FStar_Syntax_Syntax.Tm_app (head',uu____4032))
            ->
            let uu____4061 = head_matches env head1 head' in
            FStar_All.pipe_right uu____4061 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____4063),uu____4064) ->
            let uu____4079 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____4079 head_match
        | (uu____4080,FStar_Syntax_Syntax.Tm_app (head1,uu____4082)) ->
            let uu____4097 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____4097 head_match
        | uu____4098 ->
            let uu____4101 =
              let uu____4106 = delta_depth_of_term env t11 in
              let uu____4108 = delta_depth_of_term env t21 in
              (uu____4106, uu____4108) in
            MisMatch uu____4101
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____4149 = FStar_Syntax_Util.head_and_args t in
    match uu____4149 with
    | (head1,uu____4161) ->
        let uu____4176 =
          let uu____4177 = FStar_Syntax_Util.un_uinst head1 in
          uu____4177.FStar_Syntax_Syntax.n in
        (match uu____4176 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____4182 =
               let uu____4183 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____4183 FStar_Option.isSome in
             if uu____4182
             then
               let uu____4193 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____4193
                 (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
             else FStar_Pervasives_Native.None
         | uu____4196 -> FStar_Pervasives_Native.None) in
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
         ),uu____4264)
        ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4274 =
             let uu____4279 = maybe_inline t11 in
             let uu____4281 = maybe_inline t21 in (uu____4279, uu____4281) in
           match uu____4274 with
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
               fail r
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.None )
               -> aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t22)
               -> aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.Some
              t22) -> aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch
        (uu____4302,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Delta_equational ))
        ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4312 =
             let uu____4317 = maybe_inline t11 in
             let uu____4319 = maybe_inline t21 in (uu____4317, uu____4319) in
           match uu____4312 with
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
        let uu____4344 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____4344 with
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
        let uu____4359 =
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
        (match uu____4359 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4374 -> fail r
    | uu____4379 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4409 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4441 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4459 = FStar_Syntax_Util.type_u () in
      match uu____4459 with
      | (t,uu____4463) ->
          let uu____4464 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____4464
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4475 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____4475 FStar_Pervasives_Native.fst
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
        let uu____4519 = head_matches env t1 t' in
        match uu____4519 with
        | MisMatch uu____4520 -> false
        | uu____4525 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4591,imp),T (t2,uu____4594)) -> (t2, imp)
                     | uu____4611 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4654  ->
                    match uu____4654 with
                    | (t2,uu____4662) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____4692 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____4692 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4745))::tcs2) ->
                       aux
                         (((let uu___148_4768 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_4768.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_4768.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4778 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___125_4809 =
                 match uu___125_4809 with
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
               let uu____4872 = decompose1 [] bs1 in
               (rebuild, matches, uu____4872))
      | uu____4900 ->
          let rebuild uu___126_4905 =
            match uu___126_4905 with
            | [] -> t1
            | uu____4907 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___127_4928  ->
    match uu___127_4928 with
    | T (t,uu____4930) -> t
    | uu____4939 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___128_4943  ->
    match uu___128_4943 with
    | T (t,uu____4945) -> FStar_Syntax_Syntax.as_arg t
    | uu____4954 -> failwith "Impossible"
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
              | (uu____5028,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____5047 = new_uvar r scope1 k in
                  (match uu____5047 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____5059 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____5074 =
                         let uu____5075 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____5075 in
                       ((T (gi_xs, mk_kind)), uu____5074))
              | (uu____5084,uu____5085,C uu____5086) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____5168 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____5179;
                         FStar_Syntax_Syntax.pos = uu____5180;
                         FStar_Syntax_Syntax.vars = uu____5181;_})
                        ->
                        let uu____5196 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____5196 with
                         | (T (gi_xs,uu____5212),prob) ->
                             let uu____5222 =
                               let uu____5223 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____5223 in
                             (uu____5222, [prob])
                         | uu____5225 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____5235;
                         FStar_Syntax_Syntax.pos = uu____5236;
                         FStar_Syntax_Syntax.vars = uu____5237;_})
                        ->
                        let uu____5252 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____5252 with
                         | (T (gi_xs,uu____5268),prob) ->
                             let uu____5278 =
                               let uu____5279 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____5279 in
                             (uu____5278, [prob])
                         | uu____5281 -> failwith "impossible")
                    | (uu____5287,uu____5288,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____5290;
                         FStar_Syntax_Syntax.pos = uu____5291;
                         FStar_Syntax_Syntax.vars = uu____5292;_})
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
                        let uu____5367 =
                          let uu____5372 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____5372 FStar_List.unzip in
                        (match uu____5367 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5401 =
                                 let uu____5402 =
                                   let uu____5405 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____5405 un_T in
                                 let uu____5406 =
                                   let uu____5412 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____5412
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5402;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5406;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5401 in
                             ((C gi_xs), sub_probs))
                    | uu____5417 ->
                        let uu____5424 = sub_prob scope1 args q in
                        (match uu____5424 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____5168 with
                   | (tc,probs) ->
                       let uu____5442 =
                         match q with
                         | (FStar_Pervasives_Native.Some
                            b,uu____5468,uu____5469) ->
                             let uu____5477 =
                               let uu____5481 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____5481 :: args in
                             ((FStar_Pervasives_Native.Some b), (b ::
                               scope1), uu____5477)
                         | uu____5499 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____5442 with
                        | (bopt,scope2,args1) ->
                            let uu____5542 = aux scope2 args1 qs2 in
                            (match uu____5542 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5563 =
                                         let uu____5565 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____5565 in
                                       FStar_Syntax_Util.mk_conj_l uu____5563
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____5579 =
                                         let uu____5581 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____5582 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____5581 :: uu____5582 in
                                       FStar_Syntax_Util.mk_conj_l uu____5579 in
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
  let uu___149_5639 = p in
  let uu____5642 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____5643 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___149_5639.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5642;
    FStar_TypeChecker_Common.relation =
      (uu___149_5639.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5643;
    FStar_TypeChecker_Common.element =
      (uu___149_5639.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___149_5639.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___149_5639.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___149_5639.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___149_5639.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___149_5639.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5655 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____5655
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____5660 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5676 = compress_prob wl pr in
        FStar_All.pipe_right uu____5676 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5682 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____5682 with
           | (lh,uu____5695) ->
               let uu____5710 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____5710 with
                | (rh,uu____5723) ->
                    let uu____5738 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5747,FStar_Syntax_Syntax.Tm_uvar uu____5748)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5771,uu____5772)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5785,FStar_Syntax_Syntax.Tm_uvar uu____5786)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5799,uu____5800)
                          ->
                          let uu____5811 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5811 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____5851 ->
                                    let rank =
                                      let uu____5858 = is_top_level_prob prob in
                                      if uu____5858
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5860 =
                                      let uu___150_5863 = tp in
                                      let uu____5866 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___150_5863.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___150_5863.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___150_5863.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5866;
                                        FStar_TypeChecker_Common.element =
                                          (uu___150_5863.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___150_5863.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___150_5863.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___150_5863.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___150_5863.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___150_5863.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5860)))
                      | (uu____5876,FStar_Syntax_Syntax.Tm_uvar uu____5877)
                          ->
                          let uu____5888 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5888 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____5928 ->
                                    let uu____5934 =
                                      let uu___151_5939 = tp in
                                      let uu____5942 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___151_5939.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5942;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___151_5939.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___151_5939.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___151_5939.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___151_5939.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___151_5939.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___151_5939.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___151_5939.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___151_5939.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5934)))
                      | (uu____5958,uu____5959) -> (rigid_rigid, tp) in
                    (match uu____5738 with
                     | (rank,tp1) ->
                         let uu____5970 =
                           FStar_All.pipe_right
                             (let uu___152_5974 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___152_5974.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___152_5974.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___152_5974.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___152_5974.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___152_5974.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___152_5974.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___152_5974.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___152_5974.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___152_5974.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50) in
                         (rank, uu____5970))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5980 =
            FStar_All.pipe_right
              (let uu___153_5984 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___153_5984.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___153_5984.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___153_5984.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___153_5984.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___153_5984.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___153_5984.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___153_5984.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___153_5984.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___153_5984.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51) in
          (rigid_rigid, uu____5980)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____6017 probs =
      match uu____6017 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____6047 = rank wl hd1 in
               (match uu____6047 with
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
    match projectee with | UDeferred _0 -> true | uu____6118 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____6132 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____6146 -> false
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
                        let uu____6189 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____6189 with
                        | (k,uu____6193) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____6199 -> false)))
            | uu____6200 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____6247 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____6247 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____6250 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____6256 =
                     let uu____6257 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____6258 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____6257
                       uu____6258 in
                   UFailed uu____6256)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____6274 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____6274 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____6292 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____6292 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____6295 ->
                let uu____6298 =
                  let uu____6299 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____6300 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____6299
                    uu____6300 msg in
                UFailed uu____6298 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____6301,uu____6302) ->
              let uu____6303 =
                let uu____6304 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6305 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6304 uu____6305 in
              failwith uu____6303
          | (FStar_Syntax_Syntax.U_unknown ,uu____6306) ->
              let uu____6307 =
                let uu____6308 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6309 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6308 uu____6309 in
              failwith uu____6307
          | (uu____6310,FStar_Syntax_Syntax.U_bvar uu____6311) ->
              let uu____6312 =
                let uu____6313 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6314 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6313 uu____6314 in
              failwith uu____6312
          | (uu____6315,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____6316 =
                let uu____6317 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6318 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6317 uu____6318 in
              failwith uu____6316
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____6334 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____6334
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____6348 = occurs_univ v1 u3 in
              if uu____6348
              then
                let uu____6349 =
                  let uu____6350 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6351 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6350 uu____6351 in
                try_umax_components u11 u21 uu____6349
              else
                (let uu____6353 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6353)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____6365 = occurs_univ v1 u3 in
              if uu____6365
              then
                let uu____6366 =
                  let uu____6367 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6368 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6367 uu____6368 in
                try_umax_components u11 u21 uu____6366
              else
                (let uu____6370 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6370)
          | (FStar_Syntax_Syntax.U_max uu____6375,uu____6376) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6381 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6381
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____6383,FStar_Syntax_Syntax.U_max uu____6384) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6389 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6389
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6391,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6392,FStar_Syntax_Syntax.U_name
             uu____6393) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6394) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6395) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6396,FStar_Syntax_Syntax.U_succ
             uu____6397) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6398,FStar_Syntax_Syntax.U_zero
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
  let uu____6468 = bc1 in
  match uu____6468 with
  | (bs1,mk_cod1) ->
      let uu____6493 = bc2 in
      (match uu____6493 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6540 = FStar_Util.first_N n1 bs in
             match uu____6540 with
             | (bs3,rest) ->
                 let uu____6554 = mk_cod rest in (bs3, uu____6554) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____6578 =
               let uu____6582 = mk_cod1 [] in (bs1, uu____6582) in
             let uu____6584 =
               let uu____6588 = mk_cod2 [] in (bs2, uu____6588) in
             (uu____6578, uu____6584)
           else
             if l1 > l2
             then
               (let uu____6615 = curry l2 bs1 mk_cod1 in
                let uu____6625 =
                  let uu____6629 = mk_cod2 [] in (bs2, uu____6629) in
                (uu____6615, uu____6625))
             else
               (let uu____6638 =
                  let uu____6642 = mk_cod1 [] in (bs1, uu____6642) in
                let uu____6644 = curry l1 bs2 mk_cod2 in
                (uu____6638, uu____6644)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6751 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____6751
       then
         let uu____6752 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6752
       else ());
      (let uu____6754 = next_prob probs in
       match uu____6754 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___154_6767 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___154_6767.wl_deferred);
               ctr = (uu___154_6767.ctr);
               defer_ok = (uu___154_6767.defer_ok);
               smt_ok = (uu___154_6767.smt_ok);
               tcenv = (uu___154_6767.tcenv)
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
                  let uu____6774 = solve_flex_rigid_join env tp probs1 in
                  (match uu____6774 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6778 = solve_rigid_flex_meet env tp probs1 in
                     match uu____6778 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____6782,uu____6783) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6792 ->
                let uu____6797 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6829  ->
                          match uu____6829 with
                          | (c,uu____6834,uu____6835) -> c < probs.ctr)) in
                (match uu____6797 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6857 =
                            FStar_List.map
                              (fun uu____6867  ->
                                 match uu____6867 with
                                 | (uu____6873,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____6857
                      | uu____6876 ->
                          let uu____6881 =
                            let uu___155_6882 = probs in
                            let uu____6883 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6896  ->
                                      match uu____6896 with
                                      | (uu____6900,uu____6901,y) -> y)) in
                            {
                              attempting = uu____6883;
                              wl_deferred = rest;
                              ctr = (uu___155_6882.ctr);
                              defer_ok = (uu___155_6882.defer_ok);
                              smt_ok = (uu___155_6882.smt_ok);
                              tcenv = (uu___155_6882.tcenv)
                            } in
                          solve env uu____6881))))
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
            let uu____6908 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____6908 with
            | USolved wl1 ->
                let uu____6910 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____6910
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
                  let uu____6944 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6944 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6947 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6955;
                  FStar_Syntax_Syntax.pos = uu____6956;
                  FStar_Syntax_Syntax.vars = uu____6957;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6960;
                  FStar_Syntax_Syntax.pos = uu____6961;
                  FStar_Syntax_Syntax.vars = uu____6962;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6975,uu____6976) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6981,FStar_Syntax_Syntax.Tm_uinst uu____6982) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6987 -> USolved wl
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
            ((let uu____6995 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6995
              then
                let uu____6996 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6996 msg
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
        (let uu____7004 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____7004
         then
           let uu____7005 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____7005
         else ());
        (let uu____7007 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____7007 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____7049 = head_matches_delta env () t1 t2 in
               match uu____7049 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____7071 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____7097 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____7106 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____7107 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____7106, uu____7107)
                          | FStar_Pervasives_Native.None  ->
                              let uu____7110 = FStar_Syntax_Subst.compress t1 in
                              let uu____7111 = FStar_Syntax_Subst.compress t2 in
                              (uu____7110, uu____7111) in
                        (match uu____7097 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____7133 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____7133 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____7156 =
                                    let uu____7162 =
                                      let uu____7165 =
                                        let uu____7168 =
                                          let uu____7169 =
                                            let uu____7174 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____7174) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____7169 in
                                        FStar_Syntax_Syntax.mk uu____7168 in
                                      uu____7165 FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____7187 =
                                      let uu____7189 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____7189] in
                                    (uu____7162, uu____7187) in
                                  FStar_Pervasives_Native.Some uu____7156
                              | (uu____7198,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____7200)) ->
                                  let uu____7205 =
                                    let uu____7209 =
                                      let uu____7211 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____7211] in
                                    (t11, uu____7209) in
                                  FStar_Pervasives_Native.Some uu____7205
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____7217),uu____7218) ->
                                  let uu____7223 =
                                    let uu____7227 =
                                      let uu____7229 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____7229] in
                                    (t21, uu____7227) in
                                  FStar_Pervasives_Native.Some uu____7223
                              | uu____7234 ->
                                  let uu____7237 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____7237 with
                                   | (head1,uu____7252) ->
                                       let uu____7267 =
                                         let uu____7268 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____7268.FStar_Syntax_Syntax.n in
                                       (match uu____7267 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____7275;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____7277;_}
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
                                        | uu____7283 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7292) ->
                  let uu____7309 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___129_7327  ->
                            match uu___129_7327 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____7332 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____7332 with
                                      | (u',uu____7343) ->
                                          let uu____7358 =
                                            let uu____7359 = whnf env u' in
                                            uu____7359.FStar_Syntax_Syntax.n in
                                          (match uu____7358 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____7363) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____7380 -> false))
                                 | uu____7381 -> false)
                            | uu____7383 -> false)) in
                  (match uu____7309 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____7404 tps =
                         match uu____7404 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7431 =
                                    let uu____7436 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____7436 in
                                  (match uu____7431 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____7455 -> FStar_Pervasives_Native.None) in
                       let uu____7460 =
                         let uu____7465 =
                           let uu____7469 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____7469, []) in
                         make_lower_bound uu____7465 lower_bounds in
                       (match uu____7460 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____7476 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7476
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
                            ((let uu____7489 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7489
                              then
                                let wl' =
                                  let uu___156_7491 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___156_7491.wl_deferred);
                                    ctr = (uu___156_7491.ctr);
                                    defer_ok = (uu___156_7491.defer_ok);
                                    smt_ok = (uu___156_7491.smt_ok);
                                    tcenv = (uu___156_7491.tcenv)
                                  } in
                                let uu____7492 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7492
                              else ());
                             (let uu____7494 =
                                solve_t env eq_prob
                                  (let uu___157_7496 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___157_7496.wl_deferred);
                                     ctr = (uu___157_7496.ctr);
                                     defer_ok = (uu___157_7496.defer_ok);
                                     smt_ok = (uu___157_7496.smt_ok);
                                     tcenv = (uu___157_7496.tcenv)
                                   }) in
                              match uu____7494 with
                              | Success uu____7498 ->
                                  let wl1 =
                                    let uu___158_7500 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___158_7500.wl_deferred);
                                      ctr = (uu___158_7500.ctr);
                                      defer_ok = (uu___158_7500.defer_ok);
                                      smt_ok = (uu___158_7500.smt_ok);
                                      tcenv = (uu___158_7500.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____7502 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____7507 -> FStar_Pervasives_Native.None))))
              | uu____7508 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7515 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____7515
         then
           let uu____7516 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7516
         else ());
        (let uu____7518 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____7518 with
         | (u,args) ->
             let uu____7545 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____7545 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____7576 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____7576 with
                    | (h1,args1) ->
                        let uu____7604 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____7604 with
                         | (h2,uu____7617) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7636 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____7636
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____7651 =
                                          let uu____7653 =
                                            let uu____7654 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____7654 in
                                          [uu____7653] in
                                        FStar_Pervasives_Native.Some
                                          uu____7651))
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
                                       (let uu____7678 =
                                          let uu____7680 =
                                            let uu____7681 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____7681 in
                                          [uu____7680] in
                                        FStar_Pervasives_Native.Some
                                          uu____7678))
                                  else FStar_Pervasives_Native.None
                              | uu____7689 -> FStar_Pervasives_Native.None)) in
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
                             let uu____7755 =
                               let uu____7761 =
                                 let uu____7764 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____7764 in
                               (uu____7761, m1) in
                             FStar_Pervasives_Native.Some uu____7755)
                    | (uu____7773,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7775)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7807),uu____7808) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____7839 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7873) ->
                       let uu____7890 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___130_7908  ->
                                 match uu___130_7908 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____7913 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____7913 with
                                           | (u',uu____7924) ->
                                               let uu____7939 =
                                                 let uu____7940 = whnf env u' in
                                                 uu____7940.FStar_Syntax_Syntax.n in
                                               (match uu____7939 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7944) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____7961 -> false))
                                      | uu____7962 -> false)
                                 | uu____7964 -> false)) in
                       (match uu____7890 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7989 tps =
                              match uu____7989 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____8030 =
                                         let uu____8037 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____8037 in
                                       (match uu____8030 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____8072 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____8079 =
                              let uu____8086 =
                                let uu____8092 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____8092, []) in
                              make_upper_bound uu____8086 upper_bounds in
                            (match uu____8079 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____8101 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____8101
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
                                 ((let uu____8120 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____8120
                                   then
                                     let wl' =
                                       let uu___159_8122 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___159_8122.wl_deferred);
                                         ctr = (uu___159_8122.ctr);
                                         defer_ok = (uu___159_8122.defer_ok);
                                         smt_ok = (uu___159_8122.smt_ok);
                                         tcenv = (uu___159_8122.tcenv)
                                       } in
                                     let uu____8123 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____8123
                                   else ());
                                  (let uu____8125 =
                                     solve_t env eq_prob
                                       (let uu___160_8127 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___160_8127.wl_deferred);
                                          ctr = (uu___160_8127.ctr);
                                          defer_ok = (uu___160_8127.defer_ok);
                                          smt_ok = (uu___160_8127.smt_ok);
                                          tcenv = (uu___160_8127.tcenv)
                                        }) in
                                   match uu____8125 with
                                   | Success uu____8129 ->
                                       let wl1 =
                                         let uu___161_8131 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___161_8131.wl_deferred);
                                           ctr = (uu___161_8131.ctr);
                                           defer_ok =
                                             (uu___161_8131.defer_ok);
                                           smt_ok = (uu___161_8131.smt_ok);
                                           tcenv = (uu___161_8131.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____8133 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____8138 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____8139 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____8200 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____8200
                      then
                        let uu____8201 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____8201
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___162_8233 = hd1 in
                      let uu____8234 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___162_8233.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___162_8233.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____8234
                      } in
                    let hd21 =
                      let uu___163_8238 = hd2 in
                      let uu____8239 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___163_8238.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___163_8238.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____8239
                      } in
                    let prob =
                      let uu____8243 =
                        let uu____8246 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____8246 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____8243 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____8254 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____8254 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____8257 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____8257 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____8275 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____8278 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____8275 uu____8278 in
                         ((let uu____8284 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____8284
                           then
                             let uu____8285 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____8286 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____8285 uu____8286
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____8301 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____8307 = aux scope env [] bs1 bs2 in
              match uu____8307 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____8323 = compress_tprob wl problem in
        solve_t' env uu____8323 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____8356 = head_matches_delta env1 wl1 t1 t2 in
          match uu____8356 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____8373,uu____8374) ->
                   let may_relate head3 =
                     let uu____8389 =
                       let uu____8390 = FStar_Syntax_Util.un_uinst head3 in
                       uu____8390.FStar_Syntax_Syntax.n in
                     match uu____8389 with
                     | FStar_Syntax_Syntax.Tm_name uu____8393 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____8394 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____8410 -> false in
                   let uu____8411 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____8411
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
                                let uu____8428 =
                                  let uu____8429 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____8429 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____8428 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____8431 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____8431
                   else
                     (let uu____8433 =
                        let uu____8434 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____8435 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____8434 uu____8435 in
                      giveup env1 uu____8433 orig)
               | (uu____8436,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___164_8445 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___164_8445.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___164_8445.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___164_8445.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___164_8445.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___164_8445.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___164_8445.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___164_8445.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___164_8445.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____8446,FStar_Pervasives_Native.None ) ->
                   ((let uu____8453 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8453
                     then
                       let uu____8454 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____8455 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____8456 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____8457 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____8454
                         uu____8455 uu____8456 uu____8457
                     else ());
                    (let uu____8459 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____8459 with
                     | (head11,args1) ->
                         let uu____8485 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____8485 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8530 =
                                  let uu____8531 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____8532 = args_to_string args1 in
                                  let uu____8533 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____8534 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8531 uu____8532 uu____8533
                                    uu____8534 in
                                giveup env1 uu____8530 orig
                              else
                                (let uu____8536 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8542 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____8542 = FStar_Syntax_Util.Equal) in
                                 if uu____8536
                                 then
                                   let uu____8543 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____8543 with
                                   | USolved wl2 ->
                                       let uu____8545 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____8545
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8549 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____8549 with
                                    | (base1,refinement1) ->
                                        let uu____8575 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____8575 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____8629 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____8629 with
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
                                                           (fun uu____8646 
                                                              ->
                                                              fun uu____8647 
                                                                ->
                                                                match 
                                                                  (uu____8646,
                                                                    uu____8647)
                                                                with
                                                                | ((a,uu____8657),
                                                                   (a',uu____8659))
                                                                    ->
                                                                    let uu____8664
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
                                                                    uu____8664)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____8670 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8670 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8675 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___165_8709 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___165_8709.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___165_8709.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___165_8709.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___165_8709.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___165_8709.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___165_8709.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___165_8709.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___165_8709.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____8729 = p in
          match uu____8729 with
          | (((u,k),xs,c),ps,(h,uu____8740,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8789 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____8789 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8803 = h gs_xs in
                     let uu____8804 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57) in
                     FStar_Syntax_Util.abs xs1 uu____8803 uu____8804 in
                   ((let uu____8808 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8808
                     then
                       let uu____8809 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____8810 = FStar_Syntax_Print.comp_to_string c in
                       let uu____8811 = FStar_Syntax_Print.term_to_string im in
                       let uu____8812 = FStar_Syntax_Print.tag_of_term im in
                       let uu____8813 =
                         let uu____8814 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____8814
                           (FStar_String.concat ", ") in
                       let uu____8817 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8809 uu____8810 uu____8811 uu____8812
                         uu____8813 uu____8817
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___131_8835 =
          match uu___131_8835 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____8864 = p in
          match uu____8864 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8922 = FStar_List.nth ps i in
              (match uu____8922 with
               | (pi,uu____8925) ->
                   let uu____8930 = FStar_List.nth xs i in
                   (match uu____8930 with
                    | (xi,uu____8937) ->
                        let rec gs k =
                          let uu____8946 = FStar_Syntax_Util.arrow_formals k in
                          match uu____8946 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8998)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____9006 = new_uvar r xs k_a in
                                    (match uu____9006 with
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
                                         let uu____9023 = aux subst2 tl1 in
                                         (match uu____9023 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____9038 =
                                                let uu____9040 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____9040 :: gi_xs' in
                                              let uu____9041 =
                                                let uu____9043 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____9043 :: gi_ps' in
                                              (uu____9038, uu____9041))) in
                              aux [] bs in
                        let uu____9046 =
                          let uu____9047 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____9047 in
                        if uu____9046
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____9050 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____9050 with
                           | (g_xs,uu____9057) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____9064 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____9067 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58) in
                                 FStar_Syntax_Util.abs xs uu____9064
                                   uu____9067 in
                               let sub1 =
                                 let uu____9071 =
                                   let uu____9074 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____9079 =
                                     let uu____9082 =
                                       FStar_List.map
                                         (fun uu____9092  ->
                                            match uu____9092 with
                                            | (uu____9097,uu____9098,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____9082 in
                                   mk_problem (p_scope orig) orig uu____9074
                                     (p_rel orig) uu____9079
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____9071 in
                               ((let uu____9108 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____9108
                                 then
                                   let uu____9109 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____9110 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____9109 uu____9110
                                 else ());
                                (let wl2 =
                                   let uu____9113 =
                                     let uu____9115 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____9115 in
                                   solve_prob orig uu____9113
                                     [TERM (u, proj)] wl1 in
                                 let uu____9120 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____9120))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____9144 = lhs in
          match uu____9144 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____9167 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____9167 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____9193 =
                        let uu____9219 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____9219) in
                      FStar_Pervasives_Native.Some uu____9193
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____9302 =
                           let uu____9306 =
                             let uu____9307 = FStar_Syntax_Subst.compress k in
                             uu____9307.FStar_Syntax_Syntax.n in
                           (uu____9306, args) in
                         match uu____9302 with
                         | (uu____9314,[]) ->
                             let uu____9316 =
                               let uu____9322 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____9322) in
                             FStar_Pervasives_Native.Some uu____9316
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____9333,uu____9334) ->
                             let uu____9347 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9347 with
                              | (uv1,uv_args) ->
                                  let uu____9376 =
                                    let uu____9377 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9377.FStar_Syntax_Syntax.n in
                                  (match uu____9376 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9384) ->
                                       let uu____9401 =
                                         pat_vars env [] uv_args in
                                       (match uu____9401 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9417  ->
                                                      let uu____9418 =
                                                        let uu____9419 =
                                                          let uu____9420 =
                                                            let uu____9423 =
                                                              let uu____9424
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9424
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9423 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____9420 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9419 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9418)) in
                                            let c1 =
                                              let uu____9430 =
                                                let uu____9431 =
                                                  let uu____9434 =
                                                    let uu____9435 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9435
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9434 in
                                                FStar_Pervasives_Native.fst
                                                  uu____9431 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9430 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9444 =
                                                let uu____9446 =
                                                  let uu____9447 =
                                                    let uu____9450 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9450
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____9447 in
                                                FStar_Pervasives_Native.Some
                                                  uu____9446 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9444 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____9460 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9463,uu____9464)
                             ->
                             let uu____9476 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9476 with
                              | (uv1,uv_args) ->
                                  let uu____9505 =
                                    let uu____9506 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9506.FStar_Syntax_Syntax.n in
                                  (match uu____9505 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9513) ->
                                       let uu____9530 =
                                         pat_vars env [] uv_args in
                                       (match uu____9530 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9546  ->
                                                      let uu____9547 =
                                                        let uu____9548 =
                                                          let uu____9549 =
                                                            let uu____9552 =
                                                              let uu____9553
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9553
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9552 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____9549 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9548 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9547)) in
                                            let c1 =
                                              let uu____9559 =
                                                let uu____9560 =
                                                  let uu____9563 =
                                                    let uu____9564 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9564
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9563 in
                                                FStar_Pervasives_Native.fst
                                                  uu____9560 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9559 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9573 =
                                                let uu____9575 =
                                                  let uu____9576 =
                                                    let uu____9579 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9579
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____9576 in
                                                FStar_Pervasives_Native.Some
                                                  uu____9575 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9573 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____9589 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9594)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____9626 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____9626
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9650 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____9650 with
                                  | (args1,rest) ->
                                      let uu____9668 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____9668 with
                                       | (xs2,c2) ->
                                           let uu____9676 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____9676
                                             (fun uu____9690  ->
                                                match uu____9690 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9712 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____9712 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____9756 =
                                        let uu____9759 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9759 in
                                      FStar_All.pipe_right uu____9756
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____9767 ->
                             let uu____9771 =
                               let uu____9772 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____9773 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____9774 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9772 uu____9773 uu____9774 in
                             failwith uu____9771 in
                       let uu____9778 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____9778
                         (fun uu____9810  ->
                            match uu____9810 with
                            | (xs1,c1) ->
                                let uu____9838 =
                                  let uu____9861 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9861) in
                                FStar_Pervasives_Native.Some uu____9838)) in
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
                     let uu____9933 = imitate orig env wl1 st in
                     match uu____9933 with
                     | Failed uu____9938 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9944 = project orig env wl1 i st in
                      match uu____9944 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____9951) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____9965 = FStar_Syntax_Util.head_and_args t21 in
                match uu____9965 with
                | (hd1,uu____9976) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9991 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9999 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____10000 -> true
                     | uu____10010 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____10013 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____10013
                         then true
                         else
                           ((let uu____10016 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____10016
                             then
                               let uu____10017 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____10017
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____10025 =
                    let uu____10028 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____10028
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____10025 FStar_Syntax_Free.names in
                let uu____10059 = FStar_Util.set_is_empty fvs_hd in
                if uu____10059
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____10068 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____10068 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____10076 =
                            let uu____10077 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____10077 in
                          giveup_or_defer1 orig uu____10076
                        else
                          (let uu____10079 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____10079
                           then
                             let uu____10080 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____10080
                              then
                                let uu____10081 = subterms args_lhs in
                                imitate' orig env wl1 uu____10081
                              else
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
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____10086 uu____10087 uu____10088
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____10093 ->
                                        let uu____10094 = sn_binders env vars in
                                        u_abs k_uv uu____10094 t21 in
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
                               (let uu____10103 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____10103
                                then
                                  ((let uu____10105 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____10105
                                    then
                                      let uu____10106 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____10107 = names_to_string fvs1 in
                                      let uu____10108 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____10106 uu____10107 uu____10108
                                    else ());
                                   (let uu____10110 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs)
                                      uu____10110 (- (Prims.parse_int "1"))))
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
                     (let uu____10124 =
                        let uu____10125 = FStar_Syntax_Free.names t1 in
                        check_head uu____10125 t2 in
                      if uu____10124
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____10129 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____10129
                          then
                            let uu____10130 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____10130
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____10133 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____10133 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____10178 =
               match uu____10178 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k in
                   let uu____10209 = FStar_Syntax_Util.arrow_formals k1 in
                   (match uu____10209 with
                    | (all_formals,uu____10220) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____10315  ->
                                        match uu____10315 with
                                        | (x,imp) ->
                                            let uu____10322 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____10322, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____10330 = FStar_Syntax_Util.type_u () in
                                match uu____10330 with
                                | (t1,uu____10334) ->
                                    let uu____10335 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    FStar_Pervasives_Native.fst uu____10335 in
                              let uu____10338 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____10338 with
                               | (t',tm_u1) ->
                                   let uu____10345 = destruct_flex_t t' in
                                   (match uu____10345 with
                                    | (uu____10367,u1,k11,uu____10370) ->
                                        let sol =
                                          let uu____10402 =
                                            let uu____10407 =
                                              u_abs k1 all_formals t' in
                                            ((u, k1), uu____10407) in
                                          TERM uu____10402 in
                                        let t_app =
                                          FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                            pat_args1
                                            FStar_Pervasives_Native.None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10469 = pat_var_opt env pat_args hd1 in
                              (match uu____10469 with
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
                                              (fun uu____10501  ->
                                                 match uu____10501 with
                                                 | (x,uu____10505) ->
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
                                      let uu____10511 =
                                        let uu____10512 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____10512 in
                                      if uu____10511
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10516 =
                                           FStar_Util.set_add
                                             (FStar_Pervasives_Native.fst
                                                formal) pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10516 formals1
                                           tl1)))
                          | uu____10522 -> failwith "Impossible" in
                        let uu____10533 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____10533 all_formals args) in
             let solve_both_pats wl1 uu____10573 uu____10574 r =
               match (uu____10573, uu____10574) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10688 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____10688
                   then
                     let uu____10689 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____10689
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____10704 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____10704
                       then
                         let uu____10705 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____10706 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____10707 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____10708 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____10709 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10705 uu____10706 uu____10707 uu____10708
                           uu____10709
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____10757 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____10757 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10770 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____10770 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10802 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10802 in
                                  let uu____10805 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____10805 k3)
                           else
                             (let uu____10808 =
                                let uu____10809 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____10810 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____10811 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10809 uu____10810 uu____10811 in
                              failwith uu____10808) in
                       let uu____10812 =
                         let uu____10818 =
                           let uu____10826 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____10826 in
                         match uu____10818 with
                         | (bs,k1') ->
                             let uu____10844 =
                               let uu____10852 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____10852 in
                             (match uu____10844 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____10873 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____10873 in
                                  let uu____10878 =
                                    let uu____10881 =
                                      let uu____10882 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____10882.FStar_Syntax_Syntax.n in
                                    let uu____10885 =
                                      let uu____10886 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____10886.FStar_Syntax_Syntax.n in
                                    (uu____10881, uu____10885) in
                                  (match uu____10878 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10894,uu____10895) ->
                                       (k1', [sub_prob])
                                   | (uu____10899,FStar_Syntax_Syntax.Tm_type
                                      uu____10900) -> (k2', [sub_prob])
                                   | uu____10904 ->
                                       let uu____10907 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____10907 with
                                        | (t,uu____10916) ->
                                            let uu____10917 = new_uvar r zs t in
                                            (match uu____10917 with
                                             | (k_zs,uu____10926) ->
                                                 let kprob =
                                                   let uu____10928 =
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
                                                          _0_64) uu____10928 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____10812 with
                       | (k_u',sub_probs) ->
                           let uu____10942 =
                             let uu____10950 =
                               let uu____10951 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____10951 in
                             let uu____10956 =
                               let uu____10959 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____10959 in
                             let uu____10962 =
                               let uu____10965 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____10965 in
                             (uu____10950, uu____10956, uu____10962) in
                           (match uu____10942 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____10984 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____10984 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____10996 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____10996
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____11000 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____11000 with
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
             let solve_one_pat uu____11032 uu____11033 =
               match (uu____11032, uu____11033) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____11097 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____11097
                     then
                       let uu____11098 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____11099 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____11098 uu____11099
                     else ());
                    (let uu____11101 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____11101
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____11115  ->
                              fun uu____11116  ->
                                match (uu____11115, uu____11116) with
                                | ((a,uu____11126),(t21,uu____11128)) ->
                                    let uu____11133 =
                                      let uu____11136 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____11136
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____11133
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2 in
                       let guard =
                         let uu____11140 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____11140 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____11151 = occurs_check env wl (u1, k1) t21 in
                        match uu____11151 with
                        | (occurs_ok,uu____11156) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____11161 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____11161
                            then
                              let sol =
                                let uu____11163 =
                                  let uu____11168 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____11168) in
                                TERM uu____11163 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____11173 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____11173
                               then
                                 let uu____11174 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____11174 with
                                 | (sol,(uu____11184,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____11194 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____11194
                                       then
                                         let uu____11195 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____11195
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____11200 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____11202 = lhs in
             match uu____11202 with
             | (t1,u1,k1,args1) ->
                 let uu____11207 = rhs in
                 (match uu____11207 with
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
                       | uu____11233 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____11239 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____11239 with
                              | (sol,uu____11246) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____11249 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____11249
                                    then
                                      let uu____11250 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____11250
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____11255 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____11257 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____11257
        then
          let uu____11258 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____11258
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____11262 = FStar_Util.physical_equality t1 t2 in
           if uu____11262
           then
             let uu____11263 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____11263
           else
             ((let uu____11266 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____11266
               then
                 let uu____11267 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____11267
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____11270,uu____11271) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____11272,FStar_Syntax_Syntax.Tm_bvar uu____11273) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___132_11313 =
                     match uu___132_11313 with
                     | [] -> c
                     | bs ->
                         let uu____11327 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____11327 in
                   let uu____11337 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____11337 with
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
                                   let uu____11430 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____11430
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____11432 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____11432))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___133_11484 =
                     match uu___133_11484 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____11509 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____11509 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11596 =
                                   let uu____11599 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____11600 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____11599
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11600 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____11596))
               | (FStar_Syntax_Syntax.Tm_abs uu____11603,uu____11604) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11622 -> true
                     | uu____11632 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11660 =
                     let uu____11671 = maybe_eta t1 in
                     let uu____11676 = maybe_eta t2 in
                     (uu____11671, uu____11676) in
                   (match uu____11660 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_11708 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_11708.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_11708.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_11708.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_11708.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_11708.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_11708.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_11708.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_11708.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11727 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11727
                        then
                          let uu____11728 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11728 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11749 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11749
                        then
                          let uu____11750 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11750 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11755 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11766,FStar_Syntax_Syntax.Tm_abs uu____11767) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11785 -> true
                     | uu____11795 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11823 =
                     let uu____11834 = maybe_eta t1 in
                     let uu____11839 = maybe_eta t2 in
                     (uu____11834, uu____11839) in
                   (match uu____11823 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_11871 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_11871.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_11871.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_11871.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_11871.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_11871.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_11871.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_11871.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_11871.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11890 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11890
                        then
                          let uu____11891 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11891 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11912 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11912
                        then
                          let uu____11913 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11913 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11918 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11929,FStar_Syntax_Syntax.Tm_refine uu____11930) ->
                   let uu____11939 = as_refinement env wl t1 in
                   (match uu____11939 with
                    | (x1,phi1) ->
                        let uu____11944 = as_refinement env wl t2 in
                        (match uu____11944 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11950 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____11950 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____11983 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____11983
                                 (guard_on_element wl problem x11) in
                             let fallback uu____11987 =
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
                                 let uu____11993 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____11993 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____12000 =
                                   let uu____12003 =
                                     let uu____12004 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____12004 :: (p_scope orig) in
                                   mk_problem uu____12003 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____12000 in
                               let uu____12007 =
                                 solve env1
                                   (let uu___167_12009 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___167_12009.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___167_12009.smt_ok);
                                      tcenv = (uu___167_12009.tcenv)
                                    }) in
                               (match uu____12007 with
                                | Failed uu____12013 -> fallback ()
                                | Success uu____12016 ->
                                    let guard =
                                      let uu____12020 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____12023 =
                                        let uu____12024 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____12024
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____12020
                                        uu____12023 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___168_12031 = wl1 in
                                      {
                                        attempting =
                                          (uu___168_12031.attempting);
                                        wl_deferred =
                                          (uu___168_12031.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___168_12031.defer_ok);
                                        smt_ok = (uu___168_12031.smt_ok);
                                        tcenv = (uu___168_12031.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12033,FStar_Syntax_Syntax.Tm_uvar uu____12034) ->
                   let uu____12055 = destruct_flex_t t1 in
                   let uu____12056 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12055 uu____12056
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12057;
                     FStar_Syntax_Syntax.tk = uu____12058;
                     FStar_Syntax_Syntax.pos = uu____12059;
                     FStar_Syntax_Syntax.vars = uu____12060;_},uu____12061),FStar_Syntax_Syntax.Tm_uvar
                  uu____12062) ->
                   let uu____12097 = destruct_flex_t t1 in
                   let uu____12098 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12097 uu____12098
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12099,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12100;
                     FStar_Syntax_Syntax.tk = uu____12101;
                     FStar_Syntax_Syntax.pos = uu____12102;
                     FStar_Syntax_Syntax.vars = uu____12103;_},uu____12104))
                   ->
                   let uu____12139 = destruct_flex_t t1 in
                   let uu____12140 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12139 uu____12140
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12141;
                     FStar_Syntax_Syntax.tk = uu____12142;
                     FStar_Syntax_Syntax.pos = uu____12143;
                     FStar_Syntax_Syntax.vars = uu____12144;_},uu____12145),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12146;
                     FStar_Syntax_Syntax.tk = uu____12147;
                     FStar_Syntax_Syntax.pos = uu____12148;
                     FStar_Syntax_Syntax.vars = uu____12149;_},uu____12150))
                   ->
                   let uu____12199 = destruct_flex_t t1 in
                   let uu____12200 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12199 uu____12200
               | (FStar_Syntax_Syntax.Tm_uvar uu____12201,uu____12202) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12213 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____12213 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12217;
                     FStar_Syntax_Syntax.tk = uu____12218;
                     FStar_Syntax_Syntax.pos = uu____12219;
                     FStar_Syntax_Syntax.vars = uu____12220;_},uu____12221),uu____12222)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12247 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____12247 t2 wl
               | (uu____12251,FStar_Syntax_Syntax.Tm_uvar uu____12252) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____12263,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12264;
                     FStar_Syntax_Syntax.tk = uu____12265;
                     FStar_Syntax_Syntax.pos = uu____12266;
                     FStar_Syntax_Syntax.vars = uu____12267;_},uu____12268))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12293,FStar_Syntax_Syntax.Tm_type uu____12294) ->
                   solve_t' env
                     (let uu___169_12306 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12306.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12306.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12306.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12306.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12306.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12306.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12306.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12306.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12306.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12307;
                     FStar_Syntax_Syntax.tk = uu____12308;
                     FStar_Syntax_Syntax.pos = uu____12309;
                     FStar_Syntax_Syntax.vars = uu____12310;_},uu____12311),FStar_Syntax_Syntax.Tm_type
                  uu____12312) ->
                   solve_t' env
                     (let uu___169_12338 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12338.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12338.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12338.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12338.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12338.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12338.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12338.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12338.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12338.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12339,FStar_Syntax_Syntax.Tm_arrow uu____12340) ->
                   solve_t' env
                     (let uu___169_12359 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12359.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12359.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12359.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12359.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12359.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12359.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12359.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12359.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12359.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12360;
                     FStar_Syntax_Syntax.tk = uu____12361;
                     FStar_Syntax_Syntax.pos = uu____12362;
                     FStar_Syntax_Syntax.vars = uu____12363;_},uu____12364),FStar_Syntax_Syntax.Tm_arrow
                  uu____12365) ->
                   solve_t' env
                     (let uu___169_12398 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12398.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12398.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12398.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12398.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12398.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12398.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12398.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12398.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12398.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____12399,uu____12400) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12413 =
                        let uu____12414 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12414 in
                      if uu____12413
                      then
                        let uu____12415 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___170_12419 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_12419.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_12419.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_12419.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_12419.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_12419.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_12419.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_12419.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_12419.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_12419.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12420 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12415 uu____12420 t2
                          wl
                      else
                        (let uu____12425 = base_and_refinement env wl t2 in
                         match uu____12425 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____12455 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___171_12459 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_12459.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_12459.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_12459.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_12459.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_12459.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_12459.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_12459.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_12459.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_12459.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12460 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12455
                                    uu____12460 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___172_12475 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_12475.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_12475.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12478 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____12478 in
                                  let guard =
                                    let uu____12486 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____12486
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12492;
                     FStar_Syntax_Syntax.tk = uu____12493;
                     FStar_Syntax_Syntax.pos = uu____12494;
                     FStar_Syntax_Syntax.vars = uu____12495;_},uu____12496),uu____12497)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12524 =
                        let uu____12525 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12525 in
                      if uu____12524
                      then
                        let uu____12526 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___170_12530 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_12530.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_12530.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_12530.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_12530.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_12530.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_12530.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_12530.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_12530.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_12530.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12531 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12526 uu____12531 t2
                          wl
                      else
                        (let uu____12536 = base_and_refinement env wl t2 in
                         match uu____12536 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____12566 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___171_12570 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_12570.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_12570.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_12570.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_12570.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_12570.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_12570.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_12570.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_12570.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_12570.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12571 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12566
                                    uu____12571 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___172_12586 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_12586.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_12586.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12589 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____12589 in
                                  let guard =
                                    let uu____12597 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____12597
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12603,FStar_Syntax_Syntax.Tm_uvar uu____12604) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12616 = base_and_refinement env wl t1 in
                      match uu____12616 with
                      | (t_base,uu____12627) ->
                          solve_t env
                            (let uu___173_12643 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_12643.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_12643.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_12643.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_12643.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_12643.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_12643.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_12643.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_12643.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12646,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12647;
                     FStar_Syntax_Syntax.tk = uu____12648;
                     FStar_Syntax_Syntax.pos = uu____12649;
                     FStar_Syntax_Syntax.vars = uu____12650;_},uu____12651))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12677 = base_and_refinement env wl t1 in
                      match uu____12677 with
                      | (t_base,uu____12688) ->
                          solve_t env
                            (let uu___173_12704 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_12704.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_12704.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_12704.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_12704.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_12704.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_12704.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_12704.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_12704.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12707,uu____12708) ->
                   let t21 =
                     let uu____12716 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____12716 in
                   solve_t env
                     (let uu___174_12730 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_12730.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___174_12730.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___174_12730.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___174_12730.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_12730.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_12730.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_12730.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_12730.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_12730.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12731,FStar_Syntax_Syntax.Tm_refine uu____12732) ->
                   let t11 =
                     let uu____12740 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____12740 in
                   solve_t env
                     (let uu___175_12754 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_12754.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_12754.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_12754.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_12754.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_12754.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_12754.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_12754.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_12754.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_12754.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12757,uu____12758) ->
                   let head1 =
                     let uu____12776 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12776
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12807 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12807
                       FStar_Pervasives_Native.fst in
                   let uu____12835 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12835
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12844 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12844
                      then
                        let guard =
                          let uu____12851 =
                            let uu____12852 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12852 = FStar_Syntax_Util.Equal in
                          if uu____12851
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12855 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____12855) in
                        let uu____12857 = solve_prob orig guard [] wl in
                        solve env uu____12857
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12860,uu____12861) ->
                   let head1 =
                     let uu____12869 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12869
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12900 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12900
                       FStar_Pervasives_Native.fst in
                   let uu____12928 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12928
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12937 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12937
                      then
                        let guard =
                          let uu____12944 =
                            let uu____12945 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12945 = FStar_Syntax_Util.Equal in
                          if uu____12944
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12948 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____12948) in
                        let uu____12950 = solve_prob orig guard [] wl in
                        solve env uu____12950
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12953,uu____12954) ->
                   let head1 =
                     let uu____12958 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12958
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12989 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12989
                       FStar_Pervasives_Native.fst in
                   let uu____13017 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13017
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13026 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13026
                      then
                        let guard =
                          let uu____13033 =
                            let uu____13034 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13034 = FStar_Syntax_Util.Equal in
                          if uu____13033
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13037 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____13037) in
                        let uu____13039 = solve_prob orig guard [] wl in
                        solve env uu____13039
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____13042,uu____13043) ->
                   let head1 =
                     let uu____13047 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13047
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13078 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13078
                       FStar_Pervasives_Native.fst in
                   let uu____13106 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13106
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13115 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13115
                      then
                        let guard =
                          let uu____13122 =
                            let uu____13123 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13123 = FStar_Syntax_Util.Equal in
                          if uu____13122
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13126 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____13126) in
                        let uu____13128 = solve_prob orig guard [] wl in
                        solve env uu____13128
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____13131,uu____13132) ->
                   let head1 =
                     let uu____13136 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13136
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13167 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13167
                       FStar_Pervasives_Native.fst in
                   let uu____13195 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13195
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13204 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13204
                      then
                        let guard =
                          let uu____13211 =
                            let uu____13212 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13212 = FStar_Syntax_Util.Equal in
                          if uu____13211
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13215 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____13215) in
                        let uu____13217 = solve_prob orig guard [] wl in
                        solve env uu____13217
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____13220,uu____13221) ->
                   let head1 =
                     let uu____13234 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13234
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13265 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13265
                       FStar_Pervasives_Native.fst in
                   let uu____13293 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13293
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13302 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13302
                      then
                        let guard =
                          let uu____13309 =
                            let uu____13310 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13310 = FStar_Syntax_Util.Equal in
                          if uu____13309
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13313 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____13313) in
                        let uu____13315 = solve_prob orig guard [] wl in
                        solve env uu____13315
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13318,FStar_Syntax_Syntax.Tm_match uu____13319) ->
                   let head1 =
                     let uu____13337 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13337
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13368 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13368
                       FStar_Pervasives_Native.fst in
                   let uu____13396 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13396
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13405 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13405
                      then
                        let guard =
                          let uu____13412 =
                            let uu____13413 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13413 = FStar_Syntax_Util.Equal in
                          if uu____13412
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13416 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____13416) in
                        let uu____13418 = solve_prob orig guard [] wl in
                        solve env uu____13418
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13421,FStar_Syntax_Syntax.Tm_uinst uu____13422) ->
                   let head1 =
                     let uu____13430 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13430
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13461 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13461
                       FStar_Pervasives_Native.fst in
                   let uu____13489 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13489
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13498 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13498
                      then
                        let guard =
                          let uu____13505 =
                            let uu____13506 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13506 = FStar_Syntax_Util.Equal in
                          if uu____13505
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13509 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____13509) in
                        let uu____13511 = solve_prob orig guard [] wl in
                        solve env uu____13511
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13514,FStar_Syntax_Syntax.Tm_name uu____13515) ->
                   let head1 =
                     let uu____13519 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13519
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13550 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13550
                       FStar_Pervasives_Native.fst in
                   let uu____13578 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13578
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13587 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13587
                      then
                        let guard =
                          let uu____13594 =
                            let uu____13595 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13595 = FStar_Syntax_Util.Equal in
                          if uu____13594
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13598 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____13598) in
                        let uu____13600 = solve_prob orig guard [] wl in
                        solve env uu____13600
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13603,FStar_Syntax_Syntax.Tm_constant uu____13604) ->
                   let head1 =
                     let uu____13608 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13608
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13639 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13639
                       FStar_Pervasives_Native.fst in
                   let uu____13667 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13667
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13676 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13676
                      then
                        let guard =
                          let uu____13683 =
                            let uu____13684 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13684 = FStar_Syntax_Util.Equal in
                          if uu____13683
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13687 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____13687) in
                        let uu____13689 = solve_prob orig guard [] wl in
                        solve env uu____13689
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13692,FStar_Syntax_Syntax.Tm_fvar uu____13693) ->
                   let head1 =
                     let uu____13697 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13697
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13728 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13728
                       FStar_Pervasives_Native.fst in
                   let uu____13756 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13756
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13765 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13765
                      then
                        let guard =
                          let uu____13772 =
                            let uu____13773 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13773 = FStar_Syntax_Util.Equal in
                          if uu____13772
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13776 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____13776) in
                        let uu____13778 = solve_prob orig guard [] wl in
                        solve env uu____13778
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13781,FStar_Syntax_Syntax.Tm_app uu____13782) ->
                   let head1 =
                     let uu____13795 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13795
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13826 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13826
                       FStar_Pervasives_Native.fst in
                   let uu____13854 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13854
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13863 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13863
                      then
                        let guard =
                          let uu____13870 =
                            let uu____13871 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13871 = FStar_Syntax_Util.Equal in
                          if uu____13870
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13874 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____13874) in
                        let uu____13876 = solve_prob orig guard [] wl in
                        solve env uu____13876
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13880,uu____13881),uu____13882) ->
                   solve_t' env
                     (let uu___176_13912 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_13912.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___176_13912.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___176_13912.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___176_13912.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_13912.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_13912.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_13912.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_13912.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_13912.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13915,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13917,uu____13918)) ->
                   solve_t' env
                     (let uu___177_13948 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___177_13948.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___177_13948.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___177_13948.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___177_13948.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___177_13948.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___177_13948.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___177_13948.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___177_13948.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___177_13948.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13949,uu____13950) ->
                   let uu____13958 =
                     let uu____13959 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13960 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13959
                       uu____13960 in
                   failwith uu____13958
               | (FStar_Syntax_Syntax.Tm_meta uu____13961,uu____13962) ->
                   let uu____13967 =
                     let uu____13968 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13969 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13968
                       uu____13969 in
                   failwith uu____13967
               | (FStar_Syntax_Syntax.Tm_delayed uu____13970,uu____13971) ->
                   let uu____13986 =
                     let uu____13987 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13988 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13987
                       uu____13988 in
                   failwith uu____13986
               | (uu____13989,FStar_Syntax_Syntax.Tm_meta uu____13990) ->
                   let uu____13995 =
                     let uu____13996 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13997 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13996
                       uu____13997 in
                   failwith uu____13995
               | (uu____13998,FStar_Syntax_Syntax.Tm_delayed uu____13999) ->
                   let uu____14014 =
                     let uu____14015 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____14016 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____14015
                       uu____14016 in
                   failwith uu____14014
               | (uu____14017,FStar_Syntax_Syntax.Tm_let uu____14018) ->
                   let uu____14026 =
                     let uu____14027 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____14028 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____14027
                       uu____14028 in
                   failwith uu____14026
               | uu____14029 -> giveup env "head tag mismatch" orig)))
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
          (let uu____14061 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____14061
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____14076  ->
                  fun uu____14077  ->
                    match (uu____14076, uu____14077) with
                    | ((a1,uu____14087),(a2,uu____14089)) ->
                        let uu____14094 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_88  -> FStar_TypeChecker_Common.TProb _0_88)
                          uu____14094)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____14100 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p)
                      FStar_Pervasives_Native.fst) sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____14100 in
           let wl1 =
             solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____14121 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____14128)::[] -> wp1
              | uu____14141 ->
                  let uu____14147 =
                    let uu____14148 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____14148 in
                  failwith uu____14147 in
            let uu____14151 =
              let uu____14157 =
                let uu____14158 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____14158 in
              [uu____14157] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____14151;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____14159 = lift_c1 () in solve_eq uu____14159 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___134_14164  ->
                       match uu___134_14164 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____14165 -> false)) in
             let uu____14166 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____14190)::uu____14191,(wp2,uu____14193)::uu____14194)
                   -> (wp1, wp2)
               | uu____14235 ->
                   let uu____14248 =
                     let uu____14249 =
                       let uu____14252 =
                         let uu____14253 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____14254 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____14253 uu____14254 in
                       (uu____14252, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____14249 in
                   raise uu____14248 in
             match uu____14166 with
             | (wpc1,wpc2) ->
                 let uu____14271 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____14271
                 then
                   let uu____14274 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____14274 wl
                 else
                   (let uu____14278 =
                      let uu____14282 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____14282 in
                    match uu____14278 with
                    | (c2_decl,qualifiers) ->
                        let uu____14294 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____14294
                        then
                          let c1_repr =
                            let uu____14297 =
                              let uu____14298 =
                                let uu____14299 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____14299 in
                              let uu____14300 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14298 uu____14300 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14297 in
                          let c2_repr =
                            let uu____14302 =
                              let uu____14303 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____14304 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14303 uu____14304 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14302 in
                          let prob =
                            let uu____14306 =
                              let uu____14309 =
                                let uu____14310 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____14311 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____14310
                                  uu____14311 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____14309 in
                            FStar_TypeChecker_Common.TProb uu____14306 in
                          let wl1 =
                            let uu____14313 =
                              let uu____14315 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____14315 in
                            solve_prob orig uu____14313 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____14322 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____14322
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____14324 =
                                     let uu____14327 =
                                       let uu____14328 =
                                         let uu____14338 =
                                           let uu____14339 =
                                             let uu____14340 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____14340] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____14339 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____14341 =
                                           let uu____14343 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____14344 =
                                             let uu____14346 =
                                               let uu____14347 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____14347 in
                                             [uu____14346] in
                                           uu____14343 :: uu____14344 in
                                         (uu____14338, uu____14341) in
                                       FStar_Syntax_Syntax.Tm_app uu____14328 in
                                     FStar_Syntax_Syntax.mk uu____14327 in
                                   uu____14324
                                     (FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____14358 =
                                    let uu____14361 =
                                      let uu____14362 =
                                        let uu____14372 =
                                          let uu____14373 =
                                            let uu____14374 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____14374] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____14373 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____14375 =
                                          let uu____14377 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____14378 =
                                            let uu____14380 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____14381 =
                                              let uu____14383 =
                                                let uu____14384 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14384 in
                                              [uu____14383] in
                                            uu____14380 :: uu____14381 in
                                          uu____14377 :: uu____14378 in
                                        (uu____14372, uu____14375) in
                                      FStar_Syntax_Syntax.Tm_app uu____14362 in
                                    FStar_Syntax_Syntax.mk uu____14361 in
                                  uu____14358
                                    (FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____14395 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____14395 in
                           let wl1 =
                             let uu____14401 =
                               let uu____14403 =
                                 let uu____14406 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____14406 g in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____14403 in
                             solve_prob orig uu____14401 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____14416 = FStar_Util.physical_equality c1 c2 in
        if uu____14416
        then
          let uu____14417 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____14417
        else
          ((let uu____14420 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____14420
            then
              let uu____14421 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____14422 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14421
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14422
            else ());
           (let uu____14424 =
              let uu____14427 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____14428 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____14427, uu____14428) in
            match uu____14424 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14432),FStar_Syntax_Syntax.Total
                    (t2,uu____14434)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14447 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____14447 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14450,FStar_Syntax_Syntax.Total uu____14451) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14463),FStar_Syntax_Syntax.Total
                    (t2,uu____14465)) ->
                     let uu____14478 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____14478 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14482),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14484)) ->
                     let uu____14497 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____14497 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14501),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14503)) ->
                     let uu____14516 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____14516 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14519,FStar_Syntax_Syntax.Comp uu____14520) ->
                     let uu____14526 =
                       let uu___178_14529 = problem in
                       let uu____14532 =
                         let uu____14533 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14533 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14529.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14532;
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14529.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___178_14529.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___178_14529.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14529.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14529.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14529.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14529.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14529.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14526 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14534,FStar_Syntax_Syntax.Comp uu____14535) ->
                     let uu____14541 =
                       let uu___178_14544 = problem in
                       let uu____14547 =
                         let uu____14548 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14548 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14544.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14547;
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14544.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___178_14544.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___178_14544.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14544.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14544.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14544.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14544.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14544.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14541 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14549,FStar_Syntax_Syntax.GTotal uu____14550) ->
                     let uu____14556 =
                       let uu___179_14559 = problem in
                       let uu____14562 =
                         let uu____14563 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14563 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_14559.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___179_14559.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___179_14559.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14562;
                         FStar_TypeChecker_Common.element =
                           (uu___179_14559.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_14559.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_14559.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_14559.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_14559.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_14559.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14556 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14564,FStar_Syntax_Syntax.Total uu____14565) ->
                     let uu____14571 =
                       let uu___179_14574 = problem in
                       let uu____14577 =
                         let uu____14578 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14578 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_14574.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___179_14574.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___179_14574.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14577;
                         FStar_TypeChecker_Common.element =
                           (uu___179_14574.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_14574.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_14574.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_14574.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_14574.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_14574.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14571 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14579,FStar_Syntax_Syntax.Comp uu____14580) ->
                     let uu____14581 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____14581
                     then
                       let uu____14582 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____14582 wl
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
                           (let uu____14592 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____14592
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14594 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____14594 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____14596 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14598 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____14598) in
                                if uu____14596
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
                                  (let uu____14601 =
                                     let uu____14602 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____14603 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14602 uu____14603 in
                                   giveup env uu____14601 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14609 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14632  ->
              match uu____14632 with
              | (uu____14639,uu____14640,u,uu____14642,uu____14643,uu____14644)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____14609 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14663 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____14663 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____14673 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____14690  ->
                match uu____14690 with
                | (u1,u2) ->
                    let uu____14695 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____14696 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____14695 uu____14696)) in
      FStar_All.pipe_right uu____14673 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14710,[])) -> "{}"
      | uu____14723 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14733 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____14733
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____14736 =
              FStar_List.map
                (fun uu____14743  ->
                   match uu____14743 with
                   | (uu____14746,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____14736 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____14750 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14750 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14795 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____14795
    then
      let uu____14796 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____14797 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14796
        (rel_to_string rel) uu____14797
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
            let uu____14821 =
              let uu____14823 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____14823 in
            FStar_Syntax_Syntax.new_bv uu____14821 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____14829 =
              let uu____14831 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____14831 in
            let uu____14833 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____14829 uu____14833 in
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
          let uu____14859 = FStar_Options.eager_inference () in
          if uu____14859
          then
            let uu___180_14860 = probs in
            {
              attempting = (uu___180_14860.attempting);
              wl_deferred = (uu___180_14860.wl_deferred);
              ctr = (uu___180_14860.ctr);
              defer_ok = false;
              smt_ok = (uu___180_14860.smt_ok);
              tcenv = (uu___180_14860.tcenv)
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
             (let uu____14871 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____14871
              then
                let uu____14872 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____14872
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
          ((let uu____14884 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____14884
            then
              let uu____14885 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14885
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f in
            (let uu____14889 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____14889
             then
               let uu____14890 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14890
             else ());
            (let f2 =
               let uu____14893 =
                 let uu____14894 = FStar_Syntax_Util.unmeta f1 in
                 uu____14894.FStar_Syntax_Syntax.n in
               match uu____14893 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14898 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___181_14899 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___181_14899.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_14899.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_14899.FStar_TypeChecker_Env.implicits)
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
            let uu____14917 =
              let uu____14918 =
                let uu____14919 =
                  let uu____14920 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____14920
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14919;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____14918 in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____14917
let with_guard_no_simp env prob dopt =
  match dopt with
  | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some d ->
      let uu____14957 =
        let uu____14958 =
          let uu____14959 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst in
          FStar_All.pipe_right uu____14959
            (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
        {
          FStar_TypeChecker_Env.guard_f = uu____14958;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      FStar_Pervasives_Native.Some uu____14957
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
          (let uu____14989 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14989
           then
             let uu____14990 = FStar_Syntax_Print.term_to_string t1 in
             let uu____14991 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14990
               uu____14991
           else ());
          (let prob =
             let uu____14994 =
               let uu____14997 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____14997 in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____14994 in
           let g =
             let uu____15002 =
               let uu____15004 = singleton' env prob smt_ok in
               solve_and_commit env uu____15004
                 (fun uu____15006  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____15002 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15023 = try_teq true env t1 t2 in
        match uu____15023 with
        | FStar_Pervasives_Native.None  ->
            let uu____15025 =
              let uu____15026 =
                let uu____15029 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____15030 = FStar_TypeChecker_Env.get_range env in
                (uu____15029, uu____15030) in
              FStar_Errors.Error uu____15026 in
            raise uu____15025
        | FStar_Pervasives_Native.Some g ->
            ((let uu____15033 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____15033
              then
                let uu____15034 = FStar_Syntax_Print.term_to_string t1 in
                let uu____15035 = FStar_Syntax_Print.term_to_string t2 in
                let uu____15036 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____15034
                  uu____15035 uu____15036
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
          (let uu____15056 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____15056
           then
             let uu____15057 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____15058 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____15057
               uu____15058
           else ());
          (let uu____15060 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____15060 with
           | (prob,x) ->
               let g =
                 let uu____15068 =
                   let uu____15070 = singleton' env prob smt_ok in
                   solve_and_commit env uu____15070
                     (fun uu____15072  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____15068 in
               ((let uu____15078 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____15078
                 then
                   let uu____15079 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____15080 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____15081 =
                     let uu____15082 = FStar_Util.must g in
                     guard_to_string env uu____15082 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____15079 uu____15080 uu____15081
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
          let uu____15113 = FStar_TypeChecker_Env.get_range env in
          let uu____15114 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____15113 uu____15114
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____15129 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____15129
         then
           let uu____15130 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____15131 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____15130
             uu____15131
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____15136 =
             let uu____15139 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____15139 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____15136 in
         let uu____15142 =
           let uu____15144 = singleton env prob in
           solve_and_commit env uu____15144
             (fun uu____15146  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____15142)
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
      fun uu____15168  ->
        match uu____15168 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____15193 =
                 let uu____15194 =
                   let uu____15197 =
                     let uu____15198 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____15199 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____15198 uu____15199 in
                   let uu____15200 = FStar_TypeChecker_Env.get_range env in
                   (uu____15197, uu____15200) in
                 FStar_Errors.Error uu____15194 in
               raise uu____15193) in
            let equiv1 v1 v' =
              let uu____15208 =
                let uu____15211 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____15212 = FStar_Syntax_Subst.compress_univ v' in
                (uu____15211, uu____15212) in
              match uu____15208 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____15223 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____15242 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____15242 with
                      | FStar_Syntax_Syntax.U_unif uu____15246 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____15264  ->
                                    match uu____15264 with
                                    | (u,v') ->
                                        let uu____15270 = equiv1 v1 v' in
                                        if uu____15270
                                        then
                                          let uu____15272 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____15272 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____15282 -> [])) in
            let uu____15285 =
              let wl =
                let uu___182_15288 = empty_worklist env in
                {
                  attempting = (uu___182_15288.attempting);
                  wl_deferred = (uu___182_15288.wl_deferred);
                  ctr = (uu___182_15288.ctr);
                  defer_ok = false;
                  smt_ok = (uu___182_15288.smt_ok);
                  tcenv = (uu___182_15288.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____15300  ->
                      match uu____15300 with
                      | (lb,v1) ->
                          let uu____15305 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____15305 with
                           | USolved wl1 -> ()
                           | uu____15307 -> fail lb v1))) in
            let rec check_ineq uu____15313 =
              match uu____15313 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____15320) -> true
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
                      uu____15335,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____15337,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____15344) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____15349,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____15355 -> false) in
            let uu____15358 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____15368  ->
                      match uu____15368 with
                      | (u,v1) ->
                          let uu____15373 = check_ineq (u, v1) in
                          if uu____15373
                          then true
                          else
                            ((let uu____15376 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____15376
                              then
                                let uu____15377 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____15378 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____15377
                                  uu____15378
                              else ());
                             false))) in
            if uu____15358
            then ()
            else
              ((let uu____15382 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____15382
                then
                  ((let uu____15384 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____15384);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____15390 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____15390))
                else ());
               (let uu____15396 =
                  let uu____15397 =
                    let uu____15400 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____15400) in
                  FStar_Errors.Error uu____15397 in
                raise uu____15396))
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
      let fail uu____15437 =
        match uu____15437 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____15447 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____15447
       then
         let uu____15448 = wl_to_string wl in
         let uu____15449 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____15448 uu____15449
       else ());
      (let g1 =
         let uu____15464 = solve_and_commit env wl fail in
         match uu____15464 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___183_15471 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___183_15471.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___183_15471.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___183_15471.FStar_TypeChecker_Env.implicits)
             }
         | uu____15474 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___184_15477 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___184_15477.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___184_15477.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___184_15477.FStar_TypeChecker_Env.implicits)
        }))
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
            let uu___185_15507 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___185_15507.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___185_15507.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___185_15507.FStar_TypeChecker_Env.implicits)
            } in
          let uu____15508 =
            let uu____15509 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____15509 in
          if uu____15508
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15515 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____15515
                   then
                     let uu____15516 = FStar_TypeChecker_Env.get_range env in
                     let uu____15517 =
                       let uu____15518 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15518 in
                     FStar_Errors.diag uu____15516 uu____15517
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   let uu____15521 = check_trivial vc1 in
                   match uu____15521 with
                   | FStar_TypeChecker_Common.Trivial  ->
                       FStar_Pervasives_Native.Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then
                         ((let uu____15526 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15526
                           then
                             let uu____15527 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____15528 =
                               let uu____15529 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1
                                 "Cannot solve without SMT : %s\n"
                                 uu____15529 in
                             FStar_Errors.diag uu____15527 uu____15528
                           else ());
                          FStar_Pervasives_Native.None)
                       else
                         ((let uu____15534 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15534
                           then
                             let uu____15535 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____15536 =
                               let uu____15537 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15537 in
                             FStar_Errors.diag uu____15535 uu____15536
                           else ());
                          (let vcs =
                             let uu____15544 = FStar_Options.use_tactics () in
                             if uu____15544
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else
                               (let uu____15550 =
                                  let uu____15554 = FStar_Options.peek () in
                                  (env, vc2, uu____15554) in
                                [uu____15550]) in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____15575  ->
                                   match uu____15575 with
                                   | (env1,goal,opts) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify;
                                           FStar_TypeChecker_Normalize.Primops]
                                           env1 goal in
                                       let uu____15583 = check_trivial goal1 in
                                       (match uu____15583 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____15585 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____15585
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            (FStar_Options.push ();
                                             FStar_Options.set opts;
                                             (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                                               ();
                                             (let uu____15592 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____15592
                                              then
                                                let uu____15593 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____15594 =
                                                  let uu____15595 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____15596 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____15595 uu____15596 in
                                                FStar_Errors.diag uu____15593
                                                  uu____15594
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
      let uu____15608 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____15608 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____15613 =
            let uu____15614 =
              let uu____15617 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____15617) in
            FStar_Errors.Error uu____15614 in
          raise uu____15613
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15626 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____15626 with
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
        let uu____15643 = FStar_Syntax_Unionfind.find u in
        match uu____15643 with
        | FStar_Pervasives_Native.None  -> true
        | uu____15645 -> false in
      let rec until_fixpoint acc implicits =
        let uu____15658 = acc in
        match uu____15658 with
        | (out,changed) ->
            (match implicits with
             | [] ->
                 if Prims.op_Negation changed
                 then out
                 else until_fixpoint ([], false) out
             | hd1::tl1 ->
                 let uu____15704 = hd1 in
                 (match uu____15704 with
                  | (uu____15711,env,u,tm,k,r) ->
                      let uu____15717 = unresolved u in
                      if uu____15717
                      then until_fixpoint ((hd1 :: out), changed) tl1
                      else
                        (let env1 =
                           FStar_TypeChecker_Env.set_expected_typ env k in
                         let tm1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta] env1 tm in
                         (let uu____15735 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "RelCheck") in
                          if uu____15735
                          then
                            let uu____15736 =
                              FStar_Syntax_Print.uvar_to_string u in
                            let uu____15737 =
                              FStar_Syntax_Print.term_to_string tm1 in
                            let uu____15738 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print3
                              "Checking uvar %s resolved to %s at type %s\n"
                              uu____15736 uu____15737 uu____15738
                          else ());
                         (let env2 =
                            if forcelax
                            then
                              let uu___186_15741 = env1 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___186_15741.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___186_15741.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___186_15741.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___186_15741.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___186_15741.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___186_15741.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___186_15741.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___186_15741.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___186_15741.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___186_15741.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___186_15741.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___186_15741.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___186_15741.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___186_15741.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___186_15741.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___186_15741.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___186_15741.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___186_15741.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___186_15741.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___186_15741.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___186_15741.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___186_15741.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___186_15741.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___186_15741.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___186_15741.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___186_15741.FStar_TypeChecker_Env.is_native_tactic)
                              }
                            else env1 in
                          let uu____15743 =
                            env2.FStar_TypeChecker_Env.type_of
                              (let uu___187_15748 = env2 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___187_15748.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___187_15748.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___187_15748.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___187_15748.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___187_15748.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___187_15748.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___187_15748.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___187_15748.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___187_15748.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___187_15748.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___187_15748.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___187_15748.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___187_15748.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___187_15748.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___187_15748.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___187_15748.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___187_15748.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___187_15748.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___187_15748.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___187_15748.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___187_15748.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___187_15748.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___187_15748.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___187_15748.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___187_15748.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___187_15748.FStar_TypeChecker_Env.is_native_tactic)
                               }) tm1 in
                          match uu____15743 with
                          | (uu____15749,uu____15750,g1) ->
                              let g2 =
                                if env2.FStar_TypeChecker_Env.is_pattern
                                then
                                  let uu___188_15753 = g1 in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      FStar_TypeChecker_Common.Trivial;
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___188_15753.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___188_15753.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits =
                                      (uu___188_15753.FStar_TypeChecker_Env.implicits)
                                  }
                                else g1 in
                              let g' =
                                let uu____15756 =
                                  discharge_guard'
                                    (FStar_Pervasives_Native.Some
                                       (fun uu____15761  ->
                                          FStar_Syntax_Print.term_to_string
                                            tm1)) env2 g2 true in
                                match uu____15756 with
                                | FStar_Pervasives_Native.Some g3 -> g3
                                | FStar_Pervasives_Native.None  ->
                                    failwith
                                      "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                              until_fixpoint
                                ((FStar_List.append
                                    g'.FStar_TypeChecker_Env.implicits out),
                                  true) tl1)))) in
      let uu___189_15776 = g in
      let uu____15777 =
        until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___189_15776.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___189_15776.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs =
          (uu___189_15776.FStar_TypeChecker_Env.univ_ineqs);
        FStar_TypeChecker_Env.implicits = uu____15777
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
        let uu____15815 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____15815 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15822 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15822
      | (reason,uu____15824,uu____15825,e,t,r)::uu____15829 ->
          let uu____15843 =
            let uu____15844 =
              let uu____15847 =
                let uu____15848 = FStar_Syntax_Print.term_to_string t in
                let uu____15849 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____15848 uu____15849 in
              (uu____15847, r) in
            FStar_Errors.Error uu____15844 in
          raise uu____15843
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___190_15858 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___190_15858.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___190_15858.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___190_15858.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15879 = try_teq false env t1 t2 in
        match uu____15879 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____15882 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____15882 with
             | FStar_Pervasives_Native.Some uu____15886 -> true
             | FStar_Pervasives_Native.None  -> false)