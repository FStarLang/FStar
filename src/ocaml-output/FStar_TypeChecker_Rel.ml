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
                let uu____99 =
                  let uu____100 =
                    let uu____108 =
                      let uu____110 = FStar_Syntax_Syntax.as_arg e in
                      [uu____110] in
                    (f, uu____108) in
                  FStar_Syntax_Syntax.Tm_app uu____100 in
                FStar_Syntax_Syntax.mk uu____99 in
              uu____97 FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos in
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
          let uu___137_132 = g in
          let uu____133 =
            let uu____134 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____134 in
          {
            FStar_TypeChecker_Env.guard_f = uu____133;
            FStar_TypeChecker_Env.deferred =
              (uu___137_132.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___137_132.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___137_132.FStar_TypeChecker_Env.implicits)
          }
let trivial: FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____139 -> failwith "impossible"
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
          let uu____152 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____152
let check_trivial:
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula =
  fun t  ->
    let uu____157 =
      let uu____158 = FStar_Syntax_Util.unmeta t in
      uu____158.FStar_Syntax_Syntax.n in
    match uu____157 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____161 -> FStar_TypeChecker_Common.NonTrivial t
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
        let uu____197 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
        {
          FStar_TypeChecker_Env.guard_f = uu____197;
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
                       let uu____253 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____253
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___138_255 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___138_255.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___138_255.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___138_255.FStar_TypeChecker_Env.implicits)
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
               let uu____275 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____275
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
            let uu___139_291 = g in
            let uu____292 =
              let uu____293 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____293 in
            {
              FStar_TypeChecker_Env.guard_f = uu____292;
              FStar_TypeChecker_Env.deferred =
                (uu___139_291.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___139_291.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___139_291.FStar_TypeChecker_Env.implicits)
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
        | uu____320 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____334 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____334 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r in
            let uu____342 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                FStar_Pervasives_Native.None r in
            (uu____342, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____367 = FStar_Syntax_Util.type_u () in
        match uu____367 with
        | (t_type,u) ->
            let uu____372 =
              let uu____375 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____375 t_type in
            (match uu____372 with
             | (tt,uu____377) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____401 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____429 -> false
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
    match projectee with | Success _0 -> true | uu____579 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____595 -> false
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
    match projectee with | COVARIANT  -> true | uu____614 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____619 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____624 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___107_640  ->
    match uu___107_640 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____656 =
    let uu____657 = FStar_Syntax_Subst.compress t in
    uu____657.FStar_Syntax_Syntax.n in
  match uu____656 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____673 = FStar_Syntax_Print.uvar_to_string u in
      let uu____674 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____673 uu____674
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.pos = uu____677;
         FStar_Syntax_Syntax.vars = uu____678;_},args)
      ->
      let uu____702 = FStar_Syntax_Print.uvar_to_string u in
      let uu____703 = FStar_Syntax_Print.term_to_string ty in
      let uu____704 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" uu____702 uu____703 uu____704
  | uu____705 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___108_713  ->
      match uu___108_713 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____717 =
            let uu____719 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____720 =
              let uu____722 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____723 =
                let uu____725 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____726 =
                  let uu____728 =
                    let uu____730 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____731 =
                      let uu____733 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____734 =
                        let uu____736 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (FStar_Pervasives_Native.fst
                               p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____737 =
                          let uu____739 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____739] in
                        uu____736 :: uu____737 in
                      uu____733 :: uu____734 in
                    uu____730 :: uu____731 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____728 in
                uu____725 :: uu____726 in
              uu____722 :: uu____723 in
            uu____719 :: uu____720 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____717
      | FStar_TypeChecker_Common.CProb p ->
          let uu____744 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____745 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____744
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____745
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___109_753  ->
      match uu___109_753 with
      | UNIV (u,t) ->
          let x =
            let uu____757 = FStar_Options.hide_uvar_nums () in
            if uu____757
            then "?"
            else
              (let uu____759 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____759 FStar_Util.string_of_int) in
          let uu____760 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____760
      | TERM ((u,uu____762),t) ->
          let x =
            let uu____767 = FStar_Options.hide_uvar_nums () in
            if uu____767
            then "?"
            else
              (let uu____769 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____769 FStar_Util.string_of_int) in
          let uu____770 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____770
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____781 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____781 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____790 =
      let uu____792 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____792
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____790 (FStar_String.concat ", ")
let args_to_string args =
  let uu____812 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____823  ->
            match uu____823 with
            | (x,uu____827) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right uu____812 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____833 =
      let uu____834 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____834 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____833;
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
        let uu___140_850 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___140_850.wl_deferred);
          ctr = (uu___140_850.ctr);
          defer_ok = (uu___140_850.defer_ok);
          smt_ok;
          tcenv = (uu___140_850.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___141_880 = empty_worklist env in
  let uu____881 = FStar_List.map FStar_Pervasives_Native.snd g in
  {
    attempting = uu____881;
    wl_deferred = (uu___141_880.wl_deferred);
    ctr = (uu___141_880.ctr);
    defer_ok = false;
    smt_ok = (uu___141_880.smt_ok);
    tcenv = (uu___141_880.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___142_896 = wl in
        {
          attempting = (uu___142_896.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___142_896.ctr);
          defer_ok = (uu___142_896.defer_ok);
          smt_ok = (uu___142_896.smt_ok);
          tcenv = (uu___142_896.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___143_910 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___143_910.wl_deferred);
        ctr = (uu___143_910.ctr);
        defer_ok = (uu___143_910.defer_ok);
        smt_ok = (uu___143_910.smt_ok);
        tcenv = (uu___143_910.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____924 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____924
         then
           let uu____925 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____925
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___110_930  ->
    match uu___110_930 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___144_949 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___144_949.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___144_949.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___144_949.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___144_949.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___144_949.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___144_949.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___144_949.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___111_974  ->
    match uu___111_974 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___112_992  ->
      match uu___112_992 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___113_996  ->
    match uu___113_996 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___114_1006  ->
    match uu___114_1006 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___115_1017  ->
    match uu___115_1017 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___116_1028  ->
    match uu___116_1028 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___117_1040  ->
    match uu___117_1040 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___118_1052  ->
    match uu___118_1052 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___119_1062  ->
    match uu___119_1062 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____1077 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1077 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1093  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1152 = next_pid () in
  let uu____1153 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1152;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1153;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1209 = next_pid () in
  let uu____1210 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1209;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1210;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1259 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1259;
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
        let uu____1312 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1312
        then
          let uu____1313 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1314 = prob_to_string env d in
          let uu____1315 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1313 uu____1314 uu____1315 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1320 -> failwith "impossible" in
           let uu____1321 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1329 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1330 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1329, uu____1330)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1334 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1335 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1334, uu____1335) in
           match uu____1321 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___120_1349  ->
            match uu___120_1349 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1357 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1359),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___121_1376  ->
           match uu___121_1376 with
           | UNIV uu____1378 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1382),t) ->
               let uu____1386 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1386
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
        (fun uu___122_1404  ->
           match uu___122_1404 with
           | UNIV (u',t) ->
               let uu____1408 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1408
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1411 -> FStar_Pervasives_Native.None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1420 =
        let uu____1421 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1421 in
      FStar_Syntax_Subst.compress uu____1420
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1430 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1430
let norm_arg env t =
  let uu____1452 = sn env (FStar_Pervasives_Native.fst t) in
  (uu____1452, (FStar_Pervasives_Native.snd t))
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
           (fun uu____1475  ->
              match uu____1475 with
              | (x,imp) ->
                  let uu____1482 =
                    let uu___145_1483 = x in
                    let uu____1484 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___145_1483.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___145_1483.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1484
                    } in
                  (uu____1482, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1500 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1500
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1503 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1503
        | uu____1505 -> u2 in
      let uu____1506 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1506
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
          (let uu____1606 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____1606 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.pos = uu____1616;
               FStar_Syntax_Syntax.vars = uu____1617;_} ->
               ((x1.FStar_Syntax_Syntax.sort),
                 (FStar_Pervasives_Native.Some (x1, phi1)))
           | tt ->
               let uu____1631 =
                 let uu____1632 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1633 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1632
                   uu____1633 in
               failwith uu____1631)
    | FStar_Syntax_Syntax.Tm_uinst uu____1641 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1662 =
             let uu____1663 = FStar_Syntax_Subst.compress t1' in
             uu____1663.FStar_Syntax_Syntax.n in
           match uu____1662 with
           | FStar_Syntax_Syntax.Tm_refine uu____1672 -> aux true t1'
           | uu____1676 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1685 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1703 =
             let uu____1704 = FStar_Syntax_Subst.compress t1' in
             uu____1704.FStar_Syntax_Syntax.n in
           match uu____1703 with
           | FStar_Syntax_Syntax.Tm_refine uu____1713 -> aux true t1'
           | uu____1717 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_app uu____1726 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1751 =
             let uu____1752 = FStar_Syntax_Subst.compress t1' in
             uu____1752.FStar_Syntax_Syntax.n in
           match uu____1751 with
           | FStar_Syntax_Syntax.Tm_refine uu____1761 -> aux true t1'
           | uu____1765 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_type uu____1774 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_constant uu____1783 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_name uu____1792 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1801 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1810 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_abs uu____1825 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1842 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_let uu____1859 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_match uu____1874 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_meta uu____1894 ->
        let uu____1898 =
          let uu____1899 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1900 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1899
            uu____1900 in
        failwith uu____1898
    | FStar_Syntax_Syntax.Tm_ascribed uu____1908 ->
        let uu____1922 =
          let uu____1923 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1924 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1923
            uu____1924 in
        failwith uu____1922
    | FStar_Syntax_Syntax.Tm_delayed uu____1932 ->
        let uu____1945 =
          let uu____1946 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1947 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1946
            uu____1947 in
        failwith uu____1945
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1955 =
          let uu____1956 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1957 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1956
            uu____1957 in
        failwith uu____1955 in
  let uu____1965 = whnf env t1 in aux false uu____1965
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1975 =
        let uu____1983 = empty_worklist env in
        base_and_refinement env uu____1983 t in
      FStar_All.pipe_right uu____1975 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2003 = FStar_Syntax_Syntax.null_bv t in
    (uu____2003, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____2027 = base_and_refinement env wl t in
  match uu____2027 with
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
  fun uu____2071  ->
    match uu____2071 with
    | (t_base,refopt) ->
        let uu____2086 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
        (match uu____2086 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___123_2110  ->
      match uu___123_2110 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2114 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2115 =
            let uu____2116 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____2116 in
          let uu____2117 =
            let uu____2118 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____2118 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2114 uu____2115
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2117
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2122 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2123 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____2124 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2122 uu____2123
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2124
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2129 =
      let uu____2131 =
        let uu____2133 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2147  ->
                  match uu____2147 with | (uu____2151,uu____2152,x) -> x)) in
        FStar_List.append wl.attempting uu____2133 in
      FStar_List.map (wl_prob_to_string wl) uu____2131 in
    FStar_All.pipe_right uu____2129 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2173 =
          let uu____2183 =
            let uu____2184 = FStar_Syntax_Subst.compress k in
            uu____2184.FStar_Syntax_Syntax.n in
          match uu____2183 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2226 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2226)
              else
                (let uu____2240 = FStar_Syntax_Util.abs_formals t in
                 match uu____2240 with
                 | (ys',t1,uu____2256) ->
                     let uu____2259 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2259))
          | uu____2280 ->
              let uu____2281 =
                let uu____2287 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____2287) in
              ((ys, t), uu____2281) in
        match uu____2173 with
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
                 let uu____2338 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2338 c in
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
            let uu____2366 = p_guard prob in
            match uu____2366 with
            | (uu____2369,uv) ->
                ((let uu____2372 =
                    let uu____2373 = FStar_Syntax_Subst.compress uv in
                    uu____2373.FStar_Syntax_Syntax.n in
                  match uu____2372 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2392 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2392
                        then
                          let uu____2393 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2394 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2395 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2393
                            uu____2394 uu____2395
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2397 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___146_2400 = wl in
                  {
                    attempting = (uu___146_2400.attempting);
                    wl_deferred = (uu___146_2400.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___146_2400.defer_ok);
                    smt_ok = (uu___146_2400.smt_ok);
                    tcenv = (uu___146_2400.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2416 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2416
         then
           let uu____2417 = FStar_Util.string_of_int pid in
           let uu____2418 =
             let uu____2419 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2419 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2417 uu____2418
         else ());
        commit sol;
        (let uu___147_2424 = wl in
         {
           attempting = (uu___147_2424.attempting);
           wl_deferred = (uu___147_2424.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___147_2424.defer_ok);
           smt_ok = (uu___147_2424.smt_ok);
           tcenv = (uu___147_2424.tcenv)
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
            | (uu____2457,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2465 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____2465 in
          (let uu____2469 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2469
           then
             let uu____2470 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2471 =
               let uu____2472 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2472 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2470 uu____2471
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2501 =
    let uu____2505 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2505 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2501
    (FStar_Util.for_some
       (fun uu____2525  ->
          match uu____2525 with
          | (uv,uu____2529) ->
              FStar_Syntax_Unionfind.equiv uv
                (FStar_Pervasives_Native.fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2568 = occurs wl uk t in Prims.op_Negation uu____2568 in
  let msg =
    if occurs_ok
    then FStar_Pervasives_Native.None
    else
      (let uu____2573 =
         let uu____2574 =
           FStar_Syntax_Print.uvar_to_string (FStar_Pervasives_Native.fst uk) in
         let uu____2575 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2574 uu____2575 in
       FStar_Pervasives_Native.Some uu____2573) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2630 = occurs_check env wl uk t in
  match uu____2630 with
  | (occurs_ok,msg) ->
      let uu____2647 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2647, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  ->
            fun x  -> FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2717 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2748  ->
            fun uu____2749  ->
              match (uu____2748, uu____2749) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2792 =
                    let uu____2793 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2793 in
                  if uu____2792
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2807 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2807
                     then
                       let uu____2814 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____2814)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2717 with | (isect,uu____2836) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2899  ->
          fun uu____2900  ->
            match (uu____2899, uu____2900) with
            | ((a,uu____2910),(b,uu____2912)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2961 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2970  ->
                match uu____2970 with
                | (b,uu____2974) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____2961
      then FStar_Pervasives_Native.None
      else
        FStar_Pervasives_Native.Some (a, (FStar_Pervasives_Native.snd hd1))
  | uu____2983 -> FStar_Pervasives_Native.None
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
            let uu____3028 = pat_var_opt env seen hd1 in
            (match uu____3028 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____3036 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____3036
                   then
                     let uu____3037 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____3037
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3050 =
      let uu____3051 = FStar_Syntax_Subst.compress t in
      uu____3051.FStar_Syntax_Syntax.n in
    match uu____3050 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3053 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3062;
           FStar_Syntax_Syntax.pos = uu____3063;
           FStar_Syntax_Syntax.vars = uu____3064;_},uu____3065)
        -> true
    | uu____3084 -> false
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
           FStar_Syntax_Syntax.pos = uu____3151;
           FStar_Syntax_Syntax.vars = uu____3152;_},args)
        -> (t, uv, k, args)
    | uu____3187 -> failwith "Not a flex-uvar"
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
      let uu____3231 = destruct_flex_t t in
      match uu____3231 with
      | (t1,uv,k,args) ->
          let uu____3291 = pat_vars env [] args in
          (match uu____3291 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____3341 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3387 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3412 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3417 -> false
let head_match: match_result -> match_result =
  fun uu___124_3421  ->
    match uu___124_3421 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3430 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3441 ->
          let uu____3442 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3442 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____3448 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____3464 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3469 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____3483 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____3484 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____3485 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____3494 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____3501 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3514) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3518,uu____3519) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3541) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3552;
             FStar_Syntax_Syntax.index = uu____3553;
             FStar_Syntax_Syntax.sort = t2;_},uu____3555)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3559 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3560 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3561 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3568 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3578 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____3578
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
            let uu____3600 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3600
            then FullMatch
            else
              (let uu____3602 =
                 let uu____3607 =
                   let uu____3609 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____3609 in
                 let uu____3610 =
                   let uu____3612 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____3612 in
                 (uu____3607, uu____3610) in
               MisMatch uu____3602)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3616),FStar_Syntax_Syntax.Tm_uinst (g,uu____3618)) ->
            let uu____3623 = head_matches env f g in
            FStar_All.pipe_right uu____3623 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3630),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3632)) ->
            let uu____3657 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____3657
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3662),FStar_Syntax_Syntax.Tm_refine (y,uu____3664)) ->
            let uu____3669 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3669 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3671),uu____3672) ->
            let uu____3675 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3675 head_match
        | (uu____3676,FStar_Syntax_Syntax.Tm_refine (x,uu____3678)) ->
            let uu____3681 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3681 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3682,FStar_Syntax_Syntax.Tm_type
           uu____3683) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3684,FStar_Syntax_Syntax.Tm_arrow uu____3685) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3699),FStar_Syntax_Syntax.Tm_app (head',uu____3701))
            ->
            let uu____3722 = head_matches env head1 head' in
            FStar_All.pipe_right uu____3722 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3724),uu____3725) ->
            let uu____3736 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____3736 head_match
        | (uu____3737,FStar_Syntax_Syntax.Tm_app (head1,uu____3739)) ->
            let uu____3750 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____3750 head_match
        | uu____3751 ->
            let uu____3754 =
              let uu____3759 = delta_depth_of_term env t11 in
              let uu____3761 = delta_depth_of_term env t21 in
              (uu____3759, uu____3761) in
            MisMatch uu____3754
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3802 = FStar_Syntax_Util.head_and_args t in
    match uu____3802 with
    | (head1,uu____3812) ->
        let uu____3823 =
          let uu____3824 = FStar_Syntax_Util.un_uinst head1 in
          uu____3824.FStar_Syntax_Syntax.n in
        (match uu____3823 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3828 =
               let uu____3829 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____3829 FStar_Option.isSome in
             if uu____3828
             then
               let uu____3839 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____3839
                 (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
             else FStar_Pervasives_Native.None
         | uu____3842 -> FStar_Pervasives_Native.None) in
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
         ),uu____3910)
        ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____3920 =
             let uu____3925 = maybe_inline t11 in
             let uu____3927 = maybe_inline t21 in (uu____3925, uu____3927) in
           match uu____3920 with
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
               fail r
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.None )
               -> aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t22)
               -> aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.Some
              t22) -> aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch
        (uu____3948,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Delta_equational ))
        ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____3958 =
             let uu____3963 = maybe_inline t11 in
             let uu____3965 = maybe_inline t21 in (uu____3963, uu____3965) in
           match uu____3958 with
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
        let uu____3990 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____3990 with
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
        let uu____4005 =
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
        (match uu____4005 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4020 -> fail r
    | uu____4025 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4055 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4087 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4105 = FStar_Syntax_Util.type_u () in
      match uu____4105 with
      | (t,uu____4109) ->
          let uu____4110 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____4110
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4121 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____4121 FStar_Pervasives_Native.fst
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
        let uu____4165 = head_matches env t1 t' in
        match uu____4165 with
        | MisMatch uu____4166 -> false
        | uu____4171 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4229,imp),T (t2,uu____4232)) -> (t2, imp)
                     | uu____4246 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4285  ->
                    match uu____4285 with
                    | (t2,uu____4293) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____4320 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____4320 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4370))::tcs2) ->
                       aux
                         (((let uu___148_4393 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_4393.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_4393.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4403 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___125_4433 =
                 match uu___125_4433 with
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
               let uu____4495 = decompose1 [] bs1 in
               (rebuild, matches, uu____4495))
      | uu____4522 ->
          let rebuild uu___126_4527 =
            match uu___126_4527 with
            | [] -> t1
            | uu____4529 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___127_4550  ->
    match uu___127_4550 with
    | T (t,uu____4552) -> t
    | uu____4561 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___128_4565  ->
    match uu___128_4565 with
    | T (t,uu____4567) -> FStar_Syntax_Syntax.as_arg t
    | uu____4576 -> failwith "Impossible"
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
              | (uu____4648,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4667 = new_uvar r scope1 k in
                  (match uu____4667 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4678 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____4690 =
                         let uu____4691 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____4691 in
                       ((T (gi_xs, mk_kind)), uu____4690))
              | (uu____4700,uu____4701,C uu____4702) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4782 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____4793;
                         FStar_Syntax_Syntax.vars = uu____4794;_})
                        ->
                        let uu____4806 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4806 with
                         | (T (gi_xs,uu____4821),prob) ->
                             let uu____4831 =
                               let uu____4832 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____4832 in
                             (uu____4831, [prob])
                         | uu____4834 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____4844;
                         FStar_Syntax_Syntax.vars = uu____4845;_})
                        ->
                        let uu____4857 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4857 with
                         | (T (gi_xs,uu____4872),prob) ->
                             let uu____4882 =
                               let uu____4883 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____4883 in
                             (uu____4882, [prob])
                         | uu____4885 -> failwith "impossible")
                    | (uu____4891,uu____4892,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____4894;
                         FStar_Syntax_Syntax.vars = uu____4895;_})
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
                        let uu____4967 =
                          let uu____4972 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____4972 FStar_List.unzip in
                        (match uu____4967 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5001 =
                                 let uu____5002 =
                                   let uu____5004 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____5004 un_T in
                                 let uu____5005 =
                                   let uu____5010 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____5010
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5002;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5005;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5001 in
                             ((C gi_xs), sub_probs))
                    | uu____5015 ->
                        let uu____5022 = sub_prob scope1 args q in
                        (match uu____5022 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____4782 with
                   | (tc,probs) ->
                       let uu____5040 =
                         match q with
                         | (FStar_Pervasives_Native.Some
                            b,uu____5066,uu____5067) ->
                             let uu____5075 =
                               let uu____5079 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____5079 :: args in
                             ((FStar_Pervasives_Native.Some b), (b ::
                               scope1), uu____5075)
                         | uu____5097 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____5040 with
                        | (bopt,scope2,args1) ->
                            let uu____5139 = aux scope2 args1 qs2 in
                            (match uu____5139 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5160 =
                                         let uu____5162 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____5162 in
                                       FStar_Syntax_Util.mk_conj_l uu____5160
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____5176 =
                                         let uu____5178 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____5179 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____5178 :: uu____5179 in
                                       FStar_Syntax_Util.mk_conj_l uu____5176 in
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
  let uu___149_5236 = p in
  let uu____5239 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____5240 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___149_5236.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5239;
    FStar_TypeChecker_Common.relation =
      (uu___149_5236.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5240;
    FStar_TypeChecker_Common.element =
      (uu___149_5236.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___149_5236.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___149_5236.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___149_5236.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___149_5236.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___149_5236.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5252 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____5252
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____5257 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5273 = compress_prob wl pr in
        FStar_All.pipe_right uu____5273 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5279 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____5279 with
           | (lh,uu____5290) ->
               let uu____5301 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____5301 with
                | (rh,uu____5312) ->
                    let uu____5323 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5332,FStar_Syntax_Syntax.Tm_uvar uu____5333)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5352,uu____5353)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5364,FStar_Syntax_Syntax.Tm_uvar uu____5365)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5376,uu____5377)
                          ->
                          let uu____5386 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5386 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____5419 ->
                                    let rank =
                                      let uu____5425 = is_top_level_prob prob in
                                      if uu____5425
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5427 =
                                      let uu___150_5430 = tp in
                                      let uu____5433 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___150_5430.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___150_5430.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___150_5430.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5433;
                                        FStar_TypeChecker_Common.element =
                                          (uu___150_5430.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___150_5430.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___150_5430.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___150_5430.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___150_5430.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___150_5430.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5427)))
                      | (uu____5441,FStar_Syntax_Syntax.Tm_uvar uu____5442)
                          ->
                          let uu____5451 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5451 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____5484 ->
                                    let uu____5489 =
                                      let uu___151_5493 = tp in
                                      let uu____5496 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___151_5493.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5496;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___151_5493.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___151_5493.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___151_5493.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___151_5493.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___151_5493.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___151_5493.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___151_5493.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___151_5493.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5489)))
                      | (uu____5507,uu____5508) -> (rigid_rigid, tp) in
                    (match uu____5323 with
                     | (rank,tp1) ->
                         let uu____5519 =
                           FStar_All.pipe_right
                             (let uu___152_5523 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___152_5523.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___152_5523.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___152_5523.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___152_5523.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___152_5523.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___152_5523.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___152_5523.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___152_5523.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___152_5523.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50) in
                         (rank, uu____5519))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5529 =
            FStar_All.pipe_right
              (let uu___153_5533 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___153_5533.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___153_5533.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___153_5533.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___153_5533.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___153_5533.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___153_5533.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___153_5533.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___153_5533.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___153_5533.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51) in
          (rigid_rigid, uu____5529)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____5566 probs =
      match uu____5566 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5596 = rank wl hd1 in
               (match uu____5596 with
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
    match projectee with | UDeferred _0 -> true | uu____5667 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5681 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5695 -> false
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
                        let uu____5738 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____5738 with
                        | (k,uu____5742) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____5748 -> false)))
            | uu____5749 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____5796 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____5796 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5799 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____5805 =
                     let uu____5806 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____5807 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5806
                       uu____5807 in
                   UFailed uu____5805)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5823 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5823 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5841 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5841 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____5844 ->
                let uu____5847 =
                  let uu____5848 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____5849 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5848
                    uu____5849 msg in
                UFailed uu____5847 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____5850,uu____5851) ->
              let uu____5852 =
                let uu____5853 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5854 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5853 uu____5854 in
              failwith uu____5852
          | (FStar_Syntax_Syntax.U_unknown ,uu____5855) ->
              let uu____5856 =
                let uu____5857 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5858 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5857 uu____5858 in
              failwith uu____5856
          | (uu____5859,FStar_Syntax_Syntax.U_bvar uu____5860) ->
              let uu____5861 =
                let uu____5862 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5863 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5862 uu____5863 in
              failwith uu____5861
          | (uu____5864,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____5865 =
                let uu____5866 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5867 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5866 uu____5867 in
              failwith uu____5865
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____5883 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____5883
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____5897 = occurs_univ v1 u3 in
              if uu____5897
              then
                let uu____5898 =
                  let uu____5899 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____5900 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5899 uu____5900 in
                try_umax_components u11 u21 uu____5898
              else
                (let uu____5902 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____5902)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____5914 = occurs_univ v1 u3 in
              if uu____5914
              then
                let uu____5915 =
                  let uu____5916 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____5917 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5916 uu____5917 in
                try_umax_components u11 u21 uu____5915
              else
                (let uu____5919 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____5919)
          | (FStar_Syntax_Syntax.U_max uu____5924,uu____5925) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____5930 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____5930
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____5932,FStar_Syntax_Syntax.U_max uu____5933) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____5938 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____5938
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____5940,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____5941,FStar_Syntax_Syntax.U_name
             uu____5942) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____5943) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____5944) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____5945,FStar_Syntax_Syntax.U_succ
             uu____5946) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____5947,FStar_Syntax_Syntax.U_zero
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
  let uu____6017 = bc1 in
  match uu____6017 with
  | (bs1,mk_cod1) ->
      let uu____6042 = bc2 in
      (match uu____6042 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6089 = FStar_Util.first_N n1 bs in
             match uu____6089 with
             | (bs3,rest) ->
                 let uu____6103 = mk_cod rest in (bs3, uu____6103) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____6127 =
               let uu____6131 = mk_cod1 [] in (bs1, uu____6131) in
             let uu____6133 =
               let uu____6137 = mk_cod2 [] in (bs2, uu____6137) in
             (uu____6127, uu____6133)
           else
             if l1 > l2
             then
               (let uu____6164 = curry l2 bs1 mk_cod1 in
                let uu____6174 =
                  let uu____6178 = mk_cod2 [] in (bs2, uu____6178) in
                (uu____6164, uu____6174))
             else
               (let uu____6187 =
                  let uu____6191 = mk_cod1 [] in (bs1, uu____6191) in
                let uu____6193 = curry l1 bs2 mk_cod2 in
                (uu____6187, uu____6193)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6300 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____6300
       then
         let uu____6301 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6301
       else ());
      (let uu____6303 = next_prob probs in
       match uu____6303 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___154_6316 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___154_6316.wl_deferred);
               ctr = (uu___154_6316.ctr);
               defer_ok = (uu___154_6316.defer_ok);
               smt_ok = (uu___154_6316.smt_ok);
               tcenv = (uu___154_6316.tcenv)
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
                  let uu____6323 = solve_flex_rigid_join env tp probs1 in
                  (match uu____6323 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6327 = solve_rigid_flex_meet env tp probs1 in
                     match uu____6327 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____6331,uu____6332) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6341 ->
                let uu____6346 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6378  ->
                          match uu____6378 with
                          | (c,uu____6383,uu____6384) -> c < probs.ctr)) in
                (match uu____6346 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6406 =
                            FStar_List.map
                              (fun uu____6416  ->
                                 match uu____6416 with
                                 | (uu____6422,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____6406
                      | uu____6425 ->
                          let uu____6430 =
                            let uu___155_6431 = probs in
                            let uu____6432 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6445  ->
                                      match uu____6445 with
                                      | (uu____6449,uu____6450,y) -> y)) in
                            {
                              attempting = uu____6432;
                              wl_deferred = rest;
                              ctr = (uu___155_6431.ctr);
                              defer_ok = (uu___155_6431.defer_ok);
                              smt_ok = (uu___155_6431.smt_ok);
                              tcenv = (uu___155_6431.tcenv)
                            } in
                          solve env uu____6430))))
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
            let uu____6457 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____6457 with
            | USolved wl1 ->
                let uu____6459 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____6459
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
                  let uu____6493 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6493 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6496 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____6504;
                  FStar_Syntax_Syntax.vars = uu____6505;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____6508;
                  FStar_Syntax_Syntax.vars = uu____6509;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6518,uu____6519) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6523,FStar_Syntax_Syntax.Tm_uinst uu____6524) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6528 -> USolved wl
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
            ((let uu____6536 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6536
              then
                let uu____6537 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6537 msg
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
        (let uu____6545 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6545
         then
           let uu____6546 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6546
         else ());
        (let uu____6548 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6548 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6584 = head_matches_delta env () t1 t2 in
               match uu____6584 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6606 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____6632 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____6641 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____6642 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____6641, uu____6642)
                          | FStar_Pervasives_Native.None  ->
                              let uu____6645 = FStar_Syntax_Subst.compress t1 in
                              let uu____6646 = FStar_Syntax_Subst.compress t2 in
                              (uu____6645, uu____6646) in
                        (match uu____6632 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6664 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____6664 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6682 =
                                    let uu____6687 =
                                      let uu____6689 =
                                        let uu____6691 =
                                          let uu____6692 =
                                            let uu____6696 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____6696) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6692 in
                                        FStar_Syntax_Syntax.mk uu____6691 in
                                      uu____6689 FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____6705 =
                                      let uu____6707 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____6707] in
                                    (uu____6687, uu____6705) in
                                  FStar_Pervasives_Native.Some uu____6682
                              | (uu____6714,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6716)) ->
                                  let uu____6719 =
                                    let uu____6723 =
                                      let uu____6725 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____6725] in
                                    (t11, uu____6723) in
                                  FStar_Pervasives_Native.Some uu____6719
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6731),uu____6732) ->
                                  let uu____6735 =
                                    let uu____6739 =
                                      let uu____6741 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____6741] in
                                    (t21, uu____6739) in
                                  FStar_Pervasives_Native.Some uu____6735
                              | uu____6746 ->
                                  let uu____6749 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____6749 with
                                   | (head1,uu____6762) ->
                                       let uu____6773 =
                                         let uu____6774 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____6774.FStar_Syntax_Syntax.n in
                                       (match uu____6773 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6780;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6782;_}
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
                                        | uu____6788 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6796) ->
                  let uu____6809 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___129_6827  ->
                            match uu___129_6827 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____6832 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____6832 with
                                      | (u',uu____6841) ->
                                          let uu____6852 =
                                            let uu____6853 = whnf env u' in
                                            uu____6853.FStar_Syntax_Syntax.n in
                                          (match uu____6852 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____6856) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____6869 -> false))
                                 | uu____6870 -> false)
                            | uu____6872 -> false)) in
                  (match uu____6809 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____6893 tps =
                         match uu____6893 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____6920 =
                                    let uu____6925 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____6925 in
                                  (match uu____6920 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____6944 -> FStar_Pervasives_Native.None) in
                       let uu____6949 =
                         let uu____6954 =
                           let uu____6958 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____6958, []) in
                         make_lower_bound uu____6954 lower_bounds in
                       (match uu____6949 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____6965 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____6965
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
                            ((let uu____6978 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____6978
                              then
                                let wl' =
                                  let uu___156_6980 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___156_6980.wl_deferred);
                                    ctr = (uu___156_6980.ctr);
                                    defer_ok = (uu___156_6980.defer_ok);
                                    smt_ok = (uu___156_6980.smt_ok);
                                    tcenv = (uu___156_6980.tcenv)
                                  } in
                                let uu____6981 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____6981
                              else ());
                             (let uu____6983 =
                                solve_t env eq_prob
                                  (let uu___157_6985 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___157_6985.wl_deferred);
                                     ctr = (uu___157_6985.ctr);
                                     defer_ok = (uu___157_6985.defer_ok);
                                     smt_ok = (uu___157_6985.smt_ok);
                                     tcenv = (uu___157_6985.tcenv)
                                   }) in
                              match uu____6983 with
                              | Success uu____6987 ->
                                  let wl1 =
                                    let uu___158_6989 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___158_6989.wl_deferred);
                                      ctr = (uu___158_6989.ctr);
                                      defer_ok = (uu___158_6989.defer_ok);
                                      smt_ok = (uu___158_6989.smt_ok);
                                      tcenv = (uu___158_6989.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____6991 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____6996 -> FStar_Pervasives_Native.None))))
              | uu____6997 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
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
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7005
         else ());
        (let uu____7007 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____7007 with
         | (u,args) ->
             let uu____7028 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____7028 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____7059 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____7059 with
                    | (h1,args1) ->
                        let uu____7081 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____7081 with
                         | (h2,uu____7092) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7107 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____7107
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____7121 =
                                          let uu____7123 =
                                            let uu____7124 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____7124 in
                                          [uu____7123] in
                                        FStar_Pervasives_Native.Some
                                          uu____7121))
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
                                       (let uu____7147 =
                                          let uu____7149 =
                                            let uu____7150 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____7150 in
                                          [uu____7149] in
                                        FStar_Pervasives_Native.Some
                                          uu____7147))
                                  else FStar_Pervasives_Native.None
                              | uu____7158 -> FStar_Pervasives_Native.None)) in
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
                             let uu____7212 =
                               let uu____7217 =
                                 let uu____7219 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____7219 in
                               (uu____7217, m1) in
                             FStar_Pervasives_Native.Some uu____7212)
                    | (uu____7226,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7228)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7254),uu____7255) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____7280 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7309) ->
                       let uu____7322 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___130_7340  ->
                                 match uu___130_7340 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____7345 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____7345 with
                                           | (u',uu____7354) ->
                                               let uu____7365 =
                                                 let uu____7366 = whnf env u' in
                                                 uu____7366.FStar_Syntax_Syntax.n in
                                               (match uu____7365 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7369) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____7382 -> false))
                                      | uu____7383 -> false)
                                 | uu____7385 -> false)) in
                       (match uu____7322 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7408 tps =
                              match uu____7408 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7442 =
                                         let uu____7448 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7448 in
                                       (match uu____7442 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____7475 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____7481 =
                              let uu____7487 =
                                let uu____7492 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7492, []) in
                              make_upper_bound uu____7487 upper_bounds in
                            (match uu____7481 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____7500 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7500
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
                                 ((let uu____7516 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7516
                                   then
                                     let wl' =
                                       let uu___159_7518 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___159_7518.wl_deferred);
                                         ctr = (uu___159_7518.ctr);
                                         defer_ok = (uu___159_7518.defer_ok);
                                         smt_ok = (uu___159_7518.smt_ok);
                                         tcenv = (uu___159_7518.tcenv)
                                       } in
                                     let uu____7519 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7519
                                   else ());
                                  (let uu____7521 =
                                     solve_t env eq_prob
                                       (let uu___160_7523 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___160_7523.wl_deferred);
                                          ctr = (uu___160_7523.ctr);
                                          defer_ok = (uu___160_7523.defer_ok);
                                          smt_ok = (uu___160_7523.smt_ok);
                                          tcenv = (uu___160_7523.tcenv)
                                        }) in
                                   match uu____7521 with
                                   | Success uu____7525 ->
                                       let wl1 =
                                         let uu___161_7527 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___161_7527.wl_deferred);
                                           ctr = (uu___161_7527.ctr);
                                           defer_ok =
                                             (uu___161_7527.defer_ok);
                                           smt_ok = (uu___161_7527.smt_ok);
                                           tcenv = (uu___161_7527.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____7529 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____7534 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____7535 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____7596 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____7596
                      then
                        let uu____7597 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7597
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___162_7629 = hd1 in
                      let uu____7630 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___162_7629.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___162_7629.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7630
                      } in
                    let hd21 =
                      let uu___163_7633 = hd2 in
                      let uu____7634 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___163_7633.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___163_7633.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7634
                      } in
                    let prob =
                      let uu____7637 =
                        let uu____7640 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7640 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____7637 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____7647 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7647 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____7650 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____7650 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7667 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____7670 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____7667 uu____7670 in
                         ((let uu____7676 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____7676
                           then
                             let uu____7677 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____7678 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7677 uu____7678
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7691 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____7697 = aux scope env [] bs1 bs2 in
              match uu____7697 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7713 = compress_tprob wl problem in
        solve_t' env uu____7713 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7746 = head_matches_delta env1 wl1 t1 t2 in
          match uu____7746 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7763,uu____7764) ->
                   let may_relate head3 =
                     let uu____7779 =
                       let uu____7780 = FStar_Syntax_Util.un_uinst head3 in
                       uu____7780.FStar_Syntax_Syntax.n in
                     match uu____7779 with
                     | FStar_Syntax_Syntax.Tm_name uu____7782 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____7783 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____7796 -> false in
                   let uu____7797 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____7797
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
                                let uu____7812 =
                                  let uu____7813 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____7813 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____7812 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____7815 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____7815
                   else
                     (let uu____7817 =
                        let uu____7818 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____7819 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____7818 uu____7819 in
                      giveup env1 uu____7817 orig)
               | (uu____7820,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___164_7829 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___164_7829.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___164_7829.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___164_7829.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___164_7829.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___164_7829.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___164_7829.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___164_7829.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___164_7829.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____7830,FStar_Pervasives_Native.None ) ->
                   ((let uu____7837 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____7837
                     then
                       let uu____7838 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____7839 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____7840 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____7841 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____7838
                         uu____7839 uu____7840 uu____7841
                     else ());
                    (let uu____7843 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____7843 with
                     | (head11,args1) ->
                         let uu____7863 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____7863 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____7900 =
                                  let uu____7901 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____7902 = args_to_string args1 in
                                  let uu____7903 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____7904 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____7901 uu____7902 uu____7903
                                    uu____7904 in
                                giveup env1 uu____7900 orig
                              else
                                (let uu____7906 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____7912 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____7912 = FStar_Syntax_Util.Equal) in
                                 if uu____7906
                                 then
                                   let uu____7913 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____7913 with
                                   | USolved wl2 ->
                                       let uu____7915 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____7915
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____7919 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____7919 with
                                    | (base1,refinement1) ->
                                        let uu____7939 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____7939 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____7981 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____7981 with
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
                                                           (fun uu____7998 
                                                              ->
                                                              fun uu____7999 
                                                                ->
                                                                match 
                                                                  (uu____7998,
                                                                    uu____7999)
                                                                with
                                                                | ((a,uu____8009),
                                                                   (a',uu____8011))
                                                                    ->
                                                                    let uu____8016
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
                                                                    uu____8016)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____8022 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8022 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8027 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___165_8053 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___165_8053.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___165_8053.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___165_8053.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___165_8053.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___165_8053.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___165_8053.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___165_8053.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___165_8053.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____8072 = p in
          match uu____8072 with
          | (((u,k),xs,c),ps,(h,uu____8083,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8132 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____8132 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8146 = h gs_xs in
                     let uu____8147 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57) in
                     FStar_Syntax_Util.abs xs1 uu____8146 uu____8147 in
                   ((let uu____8151 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8151
                     then
                       let uu____8152 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____8153 = FStar_Syntax_Print.comp_to_string c in
                       let uu____8154 = FStar_Syntax_Print.term_to_string im in
                       let uu____8155 = FStar_Syntax_Print.tag_of_term im in
                       let uu____8156 =
                         let uu____8157 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____8157
                           (FStar_String.concat ", ") in
                       let uu____8160 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8152 uu____8153 uu____8154 uu____8155
                         uu____8156 uu____8160
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___131_8178 =
          match uu___131_8178 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____8207 = p in
          match uu____8207 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8265 = FStar_List.nth ps i in
              (match uu____8265 with
               | (pi,uu____8268) ->
                   let uu____8271 = FStar_List.nth xs i in
                   (match uu____8271 with
                    | (xi,uu____8278) ->
                        let rec gs k =
                          let uu____8287 = FStar_Syntax_Util.arrow_formals k in
                          match uu____8287 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8336)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8344 = new_uvar r xs k_a in
                                    (match uu____8344 with
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
                                         let uu____8360 = aux subst2 tl1 in
                                         (match uu____8360 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8375 =
                                                let uu____8377 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8377 :: gi_xs' in
                                              let uu____8378 =
                                                let uu____8380 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8380 :: gi_ps' in
                                              (uu____8375, uu____8378))) in
                              aux [] bs in
                        let uu____8383 =
                          let uu____8384 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8384 in
                        if uu____8383
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____8387 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8387 with
                           | (g_xs,uu____8394) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8401 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____8404 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58) in
                                 FStar_Syntax_Util.abs xs uu____8401
                                   uu____8404 in
                               let sub1 =
                                 let uu____8408 =
                                   let uu____8411 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____8415 =
                                     let uu____8417 =
                                       FStar_List.map
                                         (fun uu____8427  ->
                                            match uu____8427 with
                                            | (uu____8432,uu____8433,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____8417 in
                                   mk_problem (p_scope orig) orig uu____8411
                                     (p_rel orig) uu____8415
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____8408 in
                               ((let uu____8442 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____8442
                                 then
                                   let uu____8443 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____8444 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8443 uu____8444
                                 else ());
                                (let wl2 =
                                   let uu____8447 =
                                     let uu____8449 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____8449 in
                                   solve_prob orig uu____8447
                                     [TERM (u, proj)] wl1 in
                                 let uu____8454 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____8454))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8478 = lhs in
          match uu____8478 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8501 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____8501 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8527 =
                        let uu____8553 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____8553) in
                      FStar_Pervasives_Native.Some uu____8527
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____8636 =
                           let uu____8640 =
                             let uu____8641 = FStar_Syntax_Subst.compress k in
                             uu____8641.FStar_Syntax_Syntax.n in
                           (uu____8640, args) in
                         match uu____8636 with
                         | (uu____8647,[]) ->
                             let uu____8649 =
                               let uu____8655 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____8655) in
                             FStar_Pervasives_Native.Some uu____8649
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____8666,uu____8667) ->
                             let uu____8678 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____8678 with
                              | (uv1,uv_args) ->
                                  let uu____8701 =
                                    let uu____8702 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____8702.FStar_Syntax_Syntax.n in
                                  (match uu____8701 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____8708) ->
                                       let uu____8721 =
                                         pat_vars env [] uv_args in
                                       (match uu____8721 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____8737  ->
                                                      let uu____8738 =
                                                        let uu____8739 =
                                                          let uu____8740 =
                                                            let uu____8743 =
                                                              let uu____8744
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____8744
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____8743 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____8740 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____8739 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____8738)) in
                                            let c1 =
                                              let uu____8750 =
                                                let uu____8751 =
                                                  let uu____8754 =
                                                    let uu____8755 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____8755
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____8754 in
                                                FStar_Pervasives_Native.fst
                                                  uu____8751 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____8750 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____8763 =
                                                let uu____8765 =
                                                  let uu____8766 =
                                                    let uu____8768 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____8768
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____8766 in
                                                FStar_Pervasives_Native.Some
                                                  uu____8765 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____8763 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____8778 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app uu____8781,uu____8782)
                             ->
                             let uu____8792 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____8792 with
                              | (uv1,uv_args) ->
                                  let uu____8815 =
                                    let uu____8816 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____8816.FStar_Syntax_Syntax.n in
                                  (match uu____8815 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____8822) ->
                                       let uu____8835 =
                                         pat_vars env [] uv_args in
                                       (match uu____8835 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____8851  ->
                                                      let uu____8852 =
                                                        let uu____8853 =
                                                          let uu____8854 =
                                                            let uu____8857 =
                                                              let uu____8858
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____8858
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____8857 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____8854 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____8853 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____8852)) in
                                            let c1 =
                                              let uu____8864 =
                                                let uu____8865 =
                                                  let uu____8868 =
                                                    let uu____8869 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____8869
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____8868 in
                                                FStar_Pervasives_Native.fst
                                                  uu____8865 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____8864 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____8877 =
                                                let uu____8879 =
                                                  let uu____8880 =
                                                    let uu____8882 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____8882
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____8880 in
                                                FStar_Pervasives_Native.Some
                                                  uu____8879 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____8877 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____8892 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____8897)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____8927 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____8927
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____8951 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____8951 with
                                  | (args1,rest) ->
                                      let uu____8969 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____8969 with
                                       | (xs2,c2) ->
                                           let uu____8977 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____8977
                                             (fun uu____8991  ->
                                                match uu____8991 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9013 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____9013 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____9054 =
                                        let uu____9057 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9057 in
                                      FStar_All.pipe_right uu____9054
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____9065 ->
                             let uu____9069 =
                               let uu____9070 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____9071 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____9072 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9070 uu____9071 uu____9072 in
                             failwith uu____9069 in
                       let uu____9076 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____9076
                         (fun uu____9108  ->
                            match uu____9108 with
                            | (xs1,c1) ->
                                let uu____9136 =
                                  let uu____9159 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9159) in
                                FStar_Pervasives_Native.Some uu____9136)) in
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
                     let uu____9231 = imitate orig env wl1 st in
                     match uu____9231 with
                     | Failed uu____9236 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9242 = project orig env wl1 i st in
                      match uu____9242 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____9249) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____9263 = FStar_Syntax_Util.head_and_args t21 in
                match uu____9263 with
                | (hd1,uu____9272) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9283 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9290 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9291 -> true
                     | uu____9300 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____9303 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____9303
                         then true
                         else
                           ((let uu____9306 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____9306
                             then
                               let uu____9307 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9307
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9315 =
                    let uu____9317 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____9317
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____9315 FStar_Syntax_Free.names in
                let uu____9340 = FStar_Util.set_is_empty fvs_hd in
                if uu____9340
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____9349 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____9349 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9357 =
                            let uu____9358 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____9358 in
                          giveup_or_defer1 orig uu____9357
                        else
                          (let uu____9360 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____9360
                           then
                             let uu____9361 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____9361
                              then
                                let uu____9362 = subterms args_lhs in
                                imitate' orig env wl1 uu____9362
                              else
                                ((let uu____9366 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____9366
                                  then
                                    let uu____9367 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____9368 = names_to_string fvs1 in
                                    let uu____9369 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9367 uu____9368 uu____9369
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9374 ->
                                        let uu____9375 = sn_binders env vars in
                                        u_abs k_uv uu____9375 t21 in
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
                               (let uu____9384 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____9384
                                then
                                  ((let uu____9386 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____9386
                                    then
                                      let uu____9387 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____9388 = names_to_string fvs1 in
                                      let uu____9389 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9387 uu____9388 uu____9389
                                    else ());
                                   (let uu____9391 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9391
                                      (- (Prims.parse_int "1"))))
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
                     (let uu____9404 =
                        let uu____9405 = FStar_Syntax_Free.names t1 in
                        check_head uu____9405 t2 in
                      if uu____9404
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____9409 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____9409
                          then
                            let uu____9410 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9410
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9413 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9413 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9456 =
               match uu____9456 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k in
                   let uu____9484 = FStar_Syntax_Util.arrow_formals k1 in
                   (match uu____9484 with
                    | (all_formals,uu____9494) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____9587  ->
                                        match uu____9587 with
                                        | (x,imp) ->
                                            let uu____9594 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____9594, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____9602 = FStar_Syntax_Util.type_u () in
                                match uu____9602 with
                                | (t1,uu____9606) ->
                                    let uu____9607 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    FStar_Pervasives_Native.fst uu____9607 in
                              let uu____9610 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____9610 with
                               | (t',tm_u1) ->
                                   let uu____9617 = destruct_flex_t t' in
                                   (match uu____9617 with
                                    | (uu____9635,u1,k11,uu____9638) ->
                                        let sol =
                                          let uu____9662 =
                                            let uu____9667 =
                                              u_abs k1 all_formals t' in
                                            ((u, k1), uu____9667) in
                                          TERM uu____9662 in
                                        let t_app =
                                          FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                            pat_args1
                                            FStar_Pervasives_Native.None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____9722 = pat_var_opt env pat_args hd1 in
                              (match uu____9722 with
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
                                              (fun uu____9754  ->
                                                 match uu____9754 with
                                                 | (x,uu____9758) ->
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
                                      let uu____9764 =
                                        let uu____9765 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____9765 in
                                      if uu____9764
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____9769 =
                                           FStar_Util.set_add
                                             (FStar_Pervasives_Native.fst
                                                formal) pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____9769 formals1
                                           tl1)))
                          | uu____9775 -> failwith "Impossible" in
                        let uu____9786 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____9786 all_formals args) in
             let solve_both_pats wl1 uu____9824 uu____9825 r =
               match (uu____9824, uu____9825) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____9929 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____9929
                   then
                     let uu____9930 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____9930
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____9945 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____9945
                       then
                         let uu____9946 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____9947 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____9948 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____9949 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____9950 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____9946 uu____9947 uu____9948 uu____9949
                           uu____9950
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____9995 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____9995 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10008 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____10008 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10039 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10039 in
                                  let uu____10041 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____10041 k3)
                           else
                             (let uu____10044 =
                                let uu____10045 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____10046 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____10047 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10045 uu____10046 uu____10047 in
                              failwith uu____10044) in
                       let uu____10048 =
                         let uu____10053 =
                           let uu____10060 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____10060 in
                         match uu____10053 with
                         | (bs,k1') ->
                             let uu____10075 =
                               let uu____10082 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____10082 in
                             (match uu____10075 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____10100 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____10100 in
                                  let uu____10105 =
                                    let uu____10108 =
                                      let uu____10109 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____10109.FStar_Syntax_Syntax.n in
                                    let uu____10111 =
                                      let uu____10112 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____10112.FStar_Syntax_Syntax.n in
                                    (uu____10108, uu____10111) in
                                  (match uu____10105 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10118,uu____10119) ->
                                       (k1', [sub_prob])
                                   | (uu____10122,FStar_Syntax_Syntax.Tm_type
                                      uu____10123) -> (k2', [sub_prob])
                                   | uu____10126 ->
                                       let uu____10129 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____10129 with
                                        | (t,uu____10137) ->
                                            let uu____10138 = new_uvar r zs t in
                                            (match uu____10138 with
                                             | (k_zs,uu____10146) ->
                                                 let kprob =
                                                   let uu____10148 =
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
                                                          _0_64) uu____10148 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____10048 with
                       | (k_u',sub_probs) ->
                           let uu____10160 =
                             let uu____10166 =
                               let uu____10167 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____10167 in
                             let uu____10172 =
                               let uu____10174 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____10174 in
                             let uu____10176 =
                               let uu____10178 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____10178 in
                             (uu____10166, uu____10172, uu____10176) in
                           (match uu____10160 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____10190 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____10190 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____10202 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____10202
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____10206 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____10206 with
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
             let solve_one_pat uu____10238 uu____10239 =
               match (uu____10238, uu____10239) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10303 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____10303
                     then
                       let uu____10304 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10305 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10304 uu____10305
                     else ());
                    (let uu____10307 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____10307
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10321  ->
                              fun uu____10322  ->
                                match (uu____10321, uu____10322) with
                                | ((a,uu____10332),(t21,uu____10334)) ->
                                    let uu____10339 =
                                      let uu____10342 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____10342
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____10339
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2 in
                       let guard =
                         let uu____10346 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____10346 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____10357 = occurs_check env wl (u1, k1) t21 in
                        match uu____10357 with
                        | (occurs_ok,uu____10362) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____10367 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____10367
                            then
                              let sol =
                                let uu____10369 =
                                  let uu____10374 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____10374) in
                                TERM uu____10369 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____10379 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____10379
                               then
                                 let uu____10380 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____10380 with
                                 | (sol,(uu____10390,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____10400 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____10400
                                       then
                                         let uu____10401 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10401
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10406 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____10408 = lhs in
             match uu____10408 with
             | (t1,u1,k1,args1) ->
                 let uu____10413 = rhs in
                 (match uu____10413 with
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
                       | uu____10439 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____10445 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____10445 with
                              | (sol,uu____10452) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____10455 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____10455
                                    then
                                      let uu____10456 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____10456
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____10461 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____10463 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____10463
        then
          let uu____10464 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____10464
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____10468 = FStar_Util.physical_equality t1 t2 in
           if uu____10468
           then
             let uu____10469 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____10469
           else
             ((let uu____10472 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____10472
               then
                 let uu____10473 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____10473
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____10476,uu____10477) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____10478,FStar_Syntax_Syntax.Tm_bvar uu____10479) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___132_10513 =
                     match uu___132_10513 with
                     | [] -> c
                     | bs ->
                         let uu____10525 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____10525 in
                   let uu____10533 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____10533 with
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
                                   let uu____10615 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____10615
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____10617 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____10617))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___133_10663 =
                     match uu___133_10663 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____10684 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____10684 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____10760 =
                                   let uu____10763 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____10764 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____10763
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____10764 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____10760))
               | (FStar_Syntax_Syntax.Tm_abs uu____10767,uu____10768) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____10783 -> true
                     | uu____10792 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____10813 =
                     let uu____10822 = maybe_eta t1 in
                     let uu____10826 = maybe_eta t2 in
                     (uu____10822, uu____10826) in
                   (match uu____10813 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_10849 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_10849.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_10849.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_10849.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_10849.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_10849.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_10849.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_10849.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_10849.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____10862 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____10862
                        then
                          let uu____10863 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____10863 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____10879 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____10879
                        then
                          let uu____10880 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____10880 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____10885 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____10894,FStar_Syntax_Syntax.Tm_abs uu____10895) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____10910 -> true
                     | uu____10919 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____10940 =
                     let uu____10949 = maybe_eta t1 in
                     let uu____10953 = maybe_eta t2 in
                     (uu____10949, uu____10953) in
                   (match uu____10940 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_10976 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_10976.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_10976.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_10976.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_10976.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_10976.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_10976.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_10976.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_10976.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____10989 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____10989
                        then
                          let uu____10990 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____10990 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11006 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11006
                        then
                          let uu____11007 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11007 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11012 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11021,FStar_Syntax_Syntax.Tm_refine uu____11022) ->
                   let uu____11029 = as_refinement env wl t1 in
                   (match uu____11029 with
                    | (x1,phi1) ->
                        let uu____11034 = as_refinement env wl t2 in
                        (match uu____11034 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11040 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____11040 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____11072 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____11072
                                 (guard_on_element wl problem x11) in
                             let fallback uu____11076 =
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
                                 let uu____11081 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____11081 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11087 =
                                   let uu____11090 =
                                     let uu____11091 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____11091 :: (p_scope orig) in
                                   mk_problem uu____11090 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____11087 in
                               let uu____11094 =
                                 solve env1
                                   (let uu___167_11096 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___167_11096.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___167_11096.smt_ok);
                                      tcenv = (uu___167_11096.tcenv)
                                    }) in
                               (match uu____11094 with
                                | Failed uu____11100 -> fallback ()
                                | Success uu____11103 ->
                                    let guard =
                                      let uu____11106 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____11109 =
                                        let uu____11110 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____11110
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____11106
                                        uu____11109 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___168_11116 = wl1 in
                                      {
                                        attempting =
                                          (uu___168_11116.attempting);
                                        wl_deferred =
                                          (uu___168_11116.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___168_11116.defer_ok);
                                        smt_ok = (uu___168_11116.smt_ok);
                                        tcenv = (uu___168_11116.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11118,FStar_Syntax_Syntax.Tm_uvar uu____11119) ->
                   let uu____11136 = destruct_flex_t t1 in
                   let uu____11137 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11136 uu____11137
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11138;
                     FStar_Syntax_Syntax.pos = uu____11139;
                     FStar_Syntax_Syntax.vars = uu____11140;_},uu____11141),FStar_Syntax_Syntax.Tm_uvar
                  uu____11142) ->
                   let uu____11169 = destruct_flex_t t1 in
                   let uu____11170 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11169 uu____11170
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11171,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11172;
                     FStar_Syntax_Syntax.pos = uu____11173;
                     FStar_Syntax_Syntax.vars = uu____11174;_},uu____11175))
                   ->
                   let uu____11202 = destruct_flex_t t1 in
                   let uu____11203 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11202 uu____11203
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11204;
                     FStar_Syntax_Syntax.pos = uu____11205;
                     FStar_Syntax_Syntax.vars = uu____11206;_},uu____11207),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11208;
                     FStar_Syntax_Syntax.pos = uu____11209;
                     FStar_Syntax_Syntax.vars = uu____11210;_},uu____11211))
                   ->
                   let uu____11248 = destruct_flex_t t1 in
                   let uu____11249 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11248 uu____11249
               | (FStar_Syntax_Syntax.Tm_uvar uu____11250,uu____11251) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11260 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11260 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11264;
                     FStar_Syntax_Syntax.pos = uu____11265;
                     FStar_Syntax_Syntax.vars = uu____11266;_},uu____11267),uu____11268)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11287 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11287 t2 wl
               | (uu____11291,FStar_Syntax_Syntax.Tm_uvar uu____11292) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____11301,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11302;
                     FStar_Syntax_Syntax.pos = uu____11303;
                     FStar_Syntax_Syntax.vars = uu____11304;_},uu____11305))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11324,FStar_Syntax_Syntax.Tm_type uu____11325) ->
                   solve_t' env
                     (let uu___169_11335 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_11335.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_11335.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_11335.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_11335.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_11335.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_11335.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_11335.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_11335.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_11335.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11336;
                     FStar_Syntax_Syntax.pos = uu____11337;
                     FStar_Syntax_Syntax.vars = uu____11338;_},uu____11339),FStar_Syntax_Syntax.Tm_type
                  uu____11340) ->
                   solve_t' env
                     (let uu___169_11360 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_11360.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_11360.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_11360.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_11360.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_11360.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_11360.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_11360.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_11360.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_11360.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11361,FStar_Syntax_Syntax.Tm_arrow uu____11362) ->
                   solve_t' env
                     (let uu___169_11378 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_11378.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_11378.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_11378.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_11378.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_11378.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_11378.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_11378.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_11378.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_11378.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11379;
                     FStar_Syntax_Syntax.pos = uu____11380;
                     FStar_Syntax_Syntax.vars = uu____11381;_},uu____11382),FStar_Syntax_Syntax.Tm_arrow
                  uu____11383) ->
                   solve_t' env
                     (let uu___169_11409 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_11409.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_11409.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_11409.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_11409.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_11409.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_11409.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_11409.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_11409.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_11409.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____11410,uu____11411) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____11422 =
                        let uu____11423 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____11423 in
                      if uu____11422
                      then
                        let uu____11424 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___170_11428 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_11428.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_11428.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_11428.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_11428.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_11428.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_11428.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_11428.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_11428.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_11428.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____11429 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____11424 uu____11429 t2
                          wl
                      else
                        (let uu____11434 = base_and_refinement env wl t2 in
                         match uu____11434 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____11457 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___171_11461 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_11461.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_11461.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_11461.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_11461.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_11461.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_11461.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_11461.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_11461.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_11461.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____11462 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____11457
                                    uu____11462 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___172_11474 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_11474.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_11474.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____11477 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____11477 in
                                  let guard =
                                    let uu____11484 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____11484
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11489;
                     FStar_Syntax_Syntax.pos = uu____11490;
                     FStar_Syntax_Syntax.vars = uu____11491;_},uu____11492),uu____11493)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____11514 =
                        let uu____11515 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____11515 in
                      if uu____11514
                      then
                        let uu____11516 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___170_11520 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_11520.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_11520.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_11520.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_11520.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_11520.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_11520.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_11520.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_11520.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_11520.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____11521 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____11516 uu____11521 t2
                          wl
                      else
                        (let uu____11526 = base_and_refinement env wl t2 in
                         match uu____11526 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____11549 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___171_11553 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_11553.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_11553.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_11553.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_11553.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_11553.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_11553.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_11553.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_11553.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_11553.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____11554 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____11549
                                    uu____11554 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___172_11566 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_11566.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_11566.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____11569 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____11569 in
                                  let guard =
                                    let uu____11576 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____11576
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____11581,FStar_Syntax_Syntax.Tm_uvar uu____11582) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____11592 = base_and_refinement env wl t1 in
                      match uu____11592 with
                      | (t_base,uu____11601) ->
                          solve_t env
                            (let uu___173_11613 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_11613.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_11613.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_11613.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_11613.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_11613.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_11613.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_11613.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_11613.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____11615,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11616;
                     FStar_Syntax_Syntax.pos = uu____11617;
                     FStar_Syntax_Syntax.vars = uu____11618;_},uu____11619))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____11639 = base_and_refinement env wl t1 in
                      match uu____11639 with
                      | (t_base,uu____11648) ->
                          solve_t env
                            (let uu___173_11660 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_11660.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_11660.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_11660.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_11660.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_11660.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_11660.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_11660.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_11660.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____11662,uu____11663) ->
                   let t21 =
                     let uu____11669 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____11669 in
                   solve_t env
                     (let uu___174_11682 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_11682.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___174_11682.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___174_11682.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___174_11682.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_11682.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_11682.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_11682.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_11682.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_11682.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____11683,FStar_Syntax_Syntax.Tm_refine uu____11684) ->
                   let t11 =
                     let uu____11690 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____11690 in
                   solve_t env
                     (let uu___175_11703 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_11703.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_11703.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_11703.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_11703.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_11703.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_11703.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_11703.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_11703.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_11703.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____11705,uu____11706) ->
                   let head1 =
                     let uu____11720 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____11720
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____11743 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____11743
                       FStar_Pervasives_Native.fst in
                   let uu____11764 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____11764
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____11773 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____11773
                      then
                        let guard =
                          let uu____11780 =
                            let uu____11781 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____11781 = FStar_Syntax_Util.Equal in
                          if uu____11780
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____11784 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____11784) in
                        let uu____11786 = solve_prob orig guard [] wl in
                        solve env uu____11786
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____11789,uu____11790) ->
                   let head1 =
                     let uu____11796 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____11796
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____11819 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____11819
                       FStar_Pervasives_Native.fst in
                   let uu____11840 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____11840
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____11849 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____11849
                      then
                        let guard =
                          let uu____11856 =
                            let uu____11857 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____11857 = FStar_Syntax_Util.Equal in
                          if uu____11856
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____11860 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____11860) in
                        let uu____11862 = solve_prob orig guard [] wl in
                        solve env uu____11862
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____11865,uu____11866) ->
                   let head1 =
                     let uu____11869 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____11869
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____11892 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____11892
                       FStar_Pervasives_Native.fst in
                   let uu____11913 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____11913
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____11922 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____11922
                      then
                        let guard =
                          let uu____11929 =
                            let uu____11930 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____11930 = FStar_Syntax_Util.Equal in
                          if uu____11929
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____11933 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____11933) in
                        let uu____11935 = solve_prob orig guard [] wl in
                        solve env uu____11935
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____11938,uu____11939) ->
                   let head1 =
                     let uu____11942 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____11942
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____11965 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____11965
                       FStar_Pervasives_Native.fst in
                   let uu____11986 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____11986
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____11995 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____11995
                      then
                        let guard =
                          let uu____12002 =
                            let uu____12003 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12003 = FStar_Syntax_Util.Equal in
                          if uu____12002
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12006 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____12006) in
                        let uu____12008 = solve_prob orig guard [] wl in
                        solve env uu____12008
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____12011,uu____12012) ->
                   let head1 =
                     let uu____12015 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12015
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12038 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12038
                       FStar_Pervasives_Native.fst in
                   let uu____12059 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12059
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12068 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12068
                      then
                        let guard =
                          let uu____12075 =
                            let uu____12076 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12076 = FStar_Syntax_Util.Equal in
                          if uu____12075
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12079 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____12079) in
                        let uu____12081 = solve_prob orig guard [] wl in
                        solve env uu____12081
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____12084,uu____12085) ->
                   let head1 =
                     let uu____12095 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12095
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12118 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12118
                       FStar_Pervasives_Native.fst in
                   let uu____12139 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12139
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12148 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12148
                      then
                        let guard =
                          let uu____12155 =
                            let uu____12156 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12156 = FStar_Syntax_Util.Equal in
                          if uu____12155
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12159 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____12159) in
                        let uu____12161 = solve_prob orig guard [] wl in
                        solve env uu____12161
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12164,FStar_Syntax_Syntax.Tm_match uu____12165) ->
                   let head1 =
                     let uu____12179 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12179
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12202 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12202
                       FStar_Pervasives_Native.fst in
                   let uu____12223 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12223
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12232 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12232
                      then
                        let guard =
                          let uu____12239 =
                            let uu____12240 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12240 = FStar_Syntax_Util.Equal in
                          if uu____12239
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12243 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____12243) in
                        let uu____12245 = solve_prob orig guard [] wl in
                        solve env uu____12245
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12248,FStar_Syntax_Syntax.Tm_uinst uu____12249) ->
                   let head1 =
                     let uu____12255 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12255
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12278 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12278
                       FStar_Pervasives_Native.fst in
                   let uu____12299 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12299
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12308 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12308
                      then
                        let guard =
                          let uu____12315 =
                            let uu____12316 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12316 = FStar_Syntax_Util.Equal in
                          if uu____12315
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12319 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____12319) in
                        let uu____12321 = solve_prob orig guard [] wl in
                        solve env uu____12321
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12324,FStar_Syntax_Syntax.Tm_name uu____12325) ->
                   let head1 =
                     let uu____12328 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12328
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12351 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12351
                       FStar_Pervasives_Native.fst in
                   let uu____12372 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12372
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12381 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12381
                      then
                        let guard =
                          let uu____12388 =
                            let uu____12389 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12389 = FStar_Syntax_Util.Equal in
                          if uu____12388
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12392 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____12392) in
                        let uu____12394 = solve_prob orig guard [] wl in
                        solve env uu____12394
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12397,FStar_Syntax_Syntax.Tm_constant uu____12398) ->
                   let head1 =
                     let uu____12401 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12401
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12424 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12424
                       FStar_Pervasives_Native.fst in
                   let uu____12445 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12445
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12454 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12454
                      then
                        let guard =
                          let uu____12461 =
                            let uu____12462 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12462 = FStar_Syntax_Util.Equal in
                          if uu____12461
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12465 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____12465) in
                        let uu____12467 = solve_prob orig guard [] wl in
                        solve env uu____12467
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12470,FStar_Syntax_Syntax.Tm_fvar uu____12471) ->
                   let head1 =
                     let uu____12474 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12474
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12497 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12497
                       FStar_Pervasives_Native.fst in
                   let uu____12518 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12518
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12527 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12527
                      then
                        let guard =
                          let uu____12534 =
                            let uu____12535 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12535 = FStar_Syntax_Util.Equal in
                          if uu____12534
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12538 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____12538) in
                        let uu____12540 = solve_prob orig guard [] wl in
                        solve env uu____12540
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12543,FStar_Syntax_Syntax.Tm_app uu____12544) ->
                   let head1 =
                     let uu____12554 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12554
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12577 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12577
                       FStar_Pervasives_Native.fst in
                   let uu____12598 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12598
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12607 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12607
                      then
                        let guard =
                          let uu____12614 =
                            let uu____12615 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12615 = FStar_Syntax_Util.Equal in
                          if uu____12614
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12618 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____12618) in
                        let uu____12620 = solve_prob orig guard [] wl in
                        solve env uu____12620
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____12624,uu____12625),uu____12626) ->
                   solve_t' env
                     (let uu___176_12648 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_12648.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___176_12648.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___176_12648.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___176_12648.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_12648.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_12648.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_12648.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_12648.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_12648.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12650,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____12652,uu____12653)) ->
                   solve_t' env
                     (let uu___177_12675 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___177_12675.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___177_12675.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___177_12675.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___177_12675.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___177_12675.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___177_12675.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___177_12675.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___177_12675.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___177_12675.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____12676,uu____12677) ->
                   let uu____12684 =
                     let uu____12685 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____12686 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____12685
                       uu____12686 in
                   failwith uu____12684
               | (FStar_Syntax_Syntax.Tm_meta uu____12687,uu____12688) ->
                   let uu____12692 =
                     let uu____12693 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____12694 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____12693
                       uu____12694 in
                   failwith uu____12692
               | (FStar_Syntax_Syntax.Tm_delayed uu____12695,uu____12696) ->
                   let uu____12709 =
                     let uu____12710 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____12711 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____12710
                       uu____12711 in
                   failwith uu____12709
               | (uu____12712,FStar_Syntax_Syntax.Tm_meta uu____12713) ->
                   let uu____12717 =
                     let uu____12718 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____12719 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____12718
                       uu____12719 in
                   failwith uu____12717
               | (uu____12720,FStar_Syntax_Syntax.Tm_delayed uu____12721) ->
                   let uu____12734 =
                     let uu____12735 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____12736 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____12735
                       uu____12736 in
                   failwith uu____12734
               | (uu____12737,FStar_Syntax_Syntax.Tm_let uu____12738) ->
                   let uu____12745 =
                     let uu____12746 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____12747 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____12746
                       uu____12747 in
                   failwith uu____12745
               | uu____12748 -> giveup env "head tag mismatch" orig)))
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
          (let uu____12780 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____12780
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____12795  ->
                  fun uu____12796  ->
                    match (uu____12795, uu____12796) with
                    | ((a1,uu____12806),(a2,uu____12808)) ->
                        let uu____12813 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_88  -> FStar_TypeChecker_Common.TProb _0_88)
                          uu____12813)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____12819 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p)
                      FStar_Pervasives_Native.fst) sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____12819 in
           let wl1 =
             solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____12840 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____12845)::[] -> wp1
              | uu____12854 ->
                  let uu____12859 =
                    let uu____12860 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____12860 in
                  failwith uu____12859 in
            let uu____12862 =
              let uu____12867 =
                let uu____12868 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____12868 in
              [uu____12867] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____12862;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____12869 = lift_c1 () in solve_eq uu____12869 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___134_12874  ->
                       match uu___134_12874 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____12875 -> false)) in
             let uu____12876 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____12894)::uu____12895,(wp2,uu____12897)::uu____12898)
                   -> (wp1, wp2)
               | uu____12927 ->
                   let uu____12938 =
                     let uu____12939 =
                       let uu____12942 =
                         let uu____12943 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____12944 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____12943 uu____12944 in
                       (uu____12942, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____12939 in
                   raise uu____12938 in
             match uu____12876 with
             | (wpc1,wpc2) ->
                 let uu____12955 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____12955
                 then
                   let uu____12957 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____12957 wl
                 else
                   (let uu____12960 =
                      let uu____12964 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____12964 in
                    match uu____12960 with
                    | (c2_decl,qualifiers) ->
                        let uu____12976 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____12976
                        then
                          let c1_repr =
                            let uu____12979 =
                              let uu____12980 =
                                let uu____12981 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____12981 in
                              let uu____12982 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____12980 uu____12982 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____12979 in
                          let c2_repr =
                            let uu____12984 =
                              let uu____12985 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____12986 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____12985 uu____12986 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____12984 in
                          let prob =
                            let uu____12988 =
                              let uu____12991 =
                                let uu____12992 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____12993 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____12992
                                  uu____12993 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____12991 in
                            FStar_TypeChecker_Common.TProb uu____12988 in
                          let wl1 =
                            let uu____12995 =
                              let uu____12997 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____12997 in
                            solve_prob orig uu____12995 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____13004 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____13004
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____13006 =
                                     let uu____13008 =
                                       let uu____13009 =
                                         let uu____13017 =
                                           let uu____13018 =
                                             let uu____13019 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____13019] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____13018 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____13020 =
                                           let uu____13022 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____13023 =
                                             let uu____13025 =
                                               let uu____13026 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____13026 in
                                             [uu____13025] in
                                           uu____13022 :: uu____13023 in
                                         (uu____13017, uu____13020) in
                                       FStar_Syntax_Syntax.Tm_app uu____13009 in
                                     FStar_Syntax_Syntax.mk uu____13008 in
                                   uu____13006 FStar_Pervasives_Native.None r))
                               else
                                 (let uu____13035 =
                                    let uu____13037 =
                                      let uu____13038 =
                                        let uu____13046 =
                                          let uu____13047 =
                                            let uu____13048 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____13048] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____13047 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____13049 =
                                          let uu____13051 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____13052 =
                                            let uu____13054 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____13055 =
                                              let uu____13057 =
                                                let uu____13058 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____13058 in
                                              [uu____13057] in
                                            uu____13054 :: uu____13055 in
                                          uu____13051 :: uu____13052 in
                                        (uu____13046, uu____13049) in
                                      FStar_Syntax_Syntax.Tm_app uu____13038 in
                                    FStar_Syntax_Syntax.mk uu____13037 in
                                  uu____13035 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____13067 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____13067 in
                           let wl1 =
                             let uu____13073 =
                               let uu____13075 =
                                 let uu____13077 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____13077 g in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____13075 in
                             solve_prob orig uu____13073 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____13084 = FStar_Util.physical_equality c1 c2 in
        if uu____13084
        then
          let uu____13085 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____13085
        else
          ((let uu____13088 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____13088
            then
              let uu____13089 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____13090 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____13089
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____13090
            else ());
           (let uu____13092 =
              let uu____13095 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____13096 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____13095, uu____13096) in
            match uu____13092 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____13100),FStar_Syntax_Syntax.Total
                    (t2,uu____13102)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____13111 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____13111 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____13113,FStar_Syntax_Syntax.Total uu____13114) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____13124),FStar_Syntax_Syntax.Total
                    (t2,uu____13126)) ->
                     let uu____13135 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____13135 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____13138),FStar_Syntax_Syntax.GTotal
                    (t2,uu____13140)) ->
                     let uu____13149 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____13149 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____13152),FStar_Syntax_Syntax.GTotal
                    (t2,uu____13154)) ->
                     let uu____13163 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____13163 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____13165,FStar_Syntax_Syntax.Comp uu____13166) ->
                     let uu____13171 =
                       let uu___178_13174 = problem in
                       let uu____13177 =
                         let uu____13178 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____13178 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_13174.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____13177;
                         FStar_TypeChecker_Common.relation =
                           (uu___178_13174.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___178_13174.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___178_13174.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_13174.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_13174.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_13174.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_13174.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_13174.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____13171 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____13179,FStar_Syntax_Syntax.Comp uu____13180) ->
                     let uu____13185 =
                       let uu___178_13188 = problem in
                       let uu____13191 =
                         let uu____13192 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____13192 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_13188.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____13191;
                         FStar_TypeChecker_Common.relation =
                           (uu___178_13188.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___178_13188.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___178_13188.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_13188.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_13188.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_13188.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_13188.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_13188.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____13185 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____13193,FStar_Syntax_Syntax.GTotal uu____13194) ->
                     let uu____13199 =
                       let uu___179_13202 = problem in
                       let uu____13205 =
                         let uu____13206 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____13206 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_13202.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___179_13202.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___179_13202.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____13205;
                         FStar_TypeChecker_Common.element =
                           (uu___179_13202.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_13202.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_13202.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_13202.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_13202.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_13202.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____13199 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____13207,FStar_Syntax_Syntax.Total uu____13208) ->
                     let uu____13213 =
                       let uu___179_13216 = problem in
                       let uu____13219 =
                         let uu____13220 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____13220 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_13216.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___179_13216.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___179_13216.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____13219;
                         FStar_TypeChecker_Common.element =
                           (uu___179_13216.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_13216.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_13216.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_13216.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_13216.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_13216.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____13213 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____13221,FStar_Syntax_Syntax.Comp uu____13222) ->
                     let uu____13223 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____13223
                     then
                       let uu____13224 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____13224 wl
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
                           (let uu____13233 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____13233
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____13235 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____13235 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____13237 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____13239 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____13239) in
                                if uu____13237
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
                                  (let uu____13242 =
                                     let uu____13243 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____13244 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____13243 uu____13244 in
                                   giveup env uu____13242 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____13250 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____13273  ->
              match uu____13273 with
              | (uu____13280,uu____13281,u,uu____13283,uu____13284,uu____13285)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____13250 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____13304 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____13304 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____13314 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____13331  ->
                match uu____13331 with
                | (u1,u2) ->
                    let uu____13336 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____13337 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____13336 uu____13337)) in
      FStar_All.pipe_right uu____13314 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____13351,[])) -> "{}"
      | uu____13364 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____13374 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____13374
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____13377 =
              FStar_List.map
                (fun uu____13384  ->
                   match uu____13384 with
                   | (uu____13387,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____13377 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____13391 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____13391 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____13436 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____13436
    then
      let uu____13437 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____13438 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____13437
        (rel_to_string rel) uu____13438
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
            let uu____13462 =
              let uu____13464 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____13464 in
            FStar_Syntax_Syntax.new_bv uu____13462 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____13470 =
              let uu____13472 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____13472 in
            let uu____13474 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____13470 uu____13474 in
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
          let uu____13500 = FStar_Options.eager_inference () in
          if uu____13500
          then
            let uu___180_13501 = probs in
            {
              attempting = (uu___180_13501.attempting);
              wl_deferred = (uu___180_13501.wl_deferred);
              ctr = (uu___180_13501.ctr);
              defer_ok = false;
              smt_ok = (uu___180_13501.smt_ok);
              tcenv = (uu___180_13501.tcenv)
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
             (let uu____13512 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____13512
              then
                let uu____13513 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____13513
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
          ((let uu____13525 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____13525
            then
              let uu____13526 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____13526
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f in
            (let uu____13530 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____13530
             then
               let uu____13531 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____13531
             else ());
            (let f2 =
               let uu____13534 =
                 let uu____13535 = FStar_Syntax_Util.unmeta f1 in
                 uu____13535.FStar_Syntax_Syntax.n in
               match uu____13534 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____13538 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___181_13539 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___181_13539.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_13539.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_13539.FStar_TypeChecker_Env.implicits)
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
            let uu____13557 =
              let uu____13558 =
                let uu____13559 =
                  let uu____13560 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____13560
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____13559;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____13558 in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____13557
let with_guard_no_simp env prob dopt =
  match dopt with
  | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some d ->
      let uu____13597 =
        let uu____13598 =
          let uu____13599 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst in
          FStar_All.pipe_right uu____13599
            (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
        {
          FStar_TypeChecker_Env.guard_f = uu____13598;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      FStar_Pervasives_Native.Some uu____13597
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
          (let uu____13629 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____13629
           then
             let uu____13630 = FStar_Syntax_Print.term_to_string t1 in
             let uu____13631 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____13630
               uu____13631
           else ());
          (let prob =
             let uu____13634 =
               let uu____13637 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____13637 in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____13634 in
           let g =
             let uu____13642 =
               let uu____13644 = singleton' env prob smt_ok in
               solve_and_commit env uu____13644
                 (fun uu____13646  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____13642 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____13663 = try_teq true env t1 t2 in
        match uu____13663 with
        | FStar_Pervasives_Native.None  ->
            let uu____13665 =
              let uu____13666 =
                let uu____13669 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____13670 = FStar_TypeChecker_Env.get_range env in
                (uu____13669, uu____13670) in
              FStar_Errors.Error uu____13666 in
            raise uu____13665
        | FStar_Pervasives_Native.Some g ->
            ((let uu____13673 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____13673
              then
                let uu____13674 = FStar_Syntax_Print.term_to_string t1 in
                let uu____13675 = FStar_Syntax_Print.term_to_string t2 in
                let uu____13676 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____13674
                  uu____13675 uu____13676
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
          (let uu____13696 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____13696
           then
             let uu____13697 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____13698 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____13697
               uu____13698
           else ());
          (let uu____13700 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____13700 with
           | (prob,x) ->
               let g =
                 let uu____13708 =
                   let uu____13710 = singleton' env prob smt_ok in
                   solve_and_commit env uu____13710
                     (fun uu____13712  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____13708 in
               ((let uu____13718 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____13718
                 then
                   let uu____13719 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____13720 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____13721 =
                     let uu____13722 = FStar_Util.must g in
                     guard_to_string env uu____13722 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____13719 uu____13720 uu____13721
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
          let uu____13753 = FStar_TypeChecker_Env.get_range env in
          let uu____13754 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____13753 uu____13754
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____13769 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____13769
         then
           let uu____13770 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____13771 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____13770
             uu____13771
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____13776 =
             let uu____13779 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____13779 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____13776 in
         let uu____13782 =
           let uu____13784 = singleton env prob in
           solve_and_commit env uu____13784
             (fun uu____13786  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____13782)
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
      fun uu____13808  ->
        match uu____13808 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____13833 =
                 let uu____13834 =
                   let uu____13837 =
                     let uu____13838 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____13839 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____13838 uu____13839 in
                   let uu____13840 = FStar_TypeChecker_Env.get_range env in
                   (uu____13837, uu____13840) in
                 FStar_Errors.Error uu____13834 in
               raise uu____13833) in
            let equiv1 v1 v' =
              let uu____13848 =
                let uu____13851 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____13852 = FStar_Syntax_Subst.compress_univ v' in
                (uu____13851, uu____13852) in
              match uu____13848 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____13863 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____13882 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____13882 with
                      | FStar_Syntax_Syntax.U_unif uu____13886 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____13904  ->
                                    match uu____13904 with
                                    | (u,v') ->
                                        let uu____13910 = equiv1 v1 v' in
                                        if uu____13910
                                        then
                                          let uu____13912 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____13912 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____13922 -> [])) in
            let uu____13925 =
              let wl =
                let uu___182_13928 = empty_worklist env in
                {
                  attempting = (uu___182_13928.attempting);
                  wl_deferred = (uu___182_13928.wl_deferred);
                  ctr = (uu___182_13928.ctr);
                  defer_ok = false;
                  smt_ok = (uu___182_13928.smt_ok);
                  tcenv = (uu___182_13928.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____13940  ->
                      match uu____13940 with
                      | (lb,v1) ->
                          let uu____13945 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____13945 with
                           | USolved wl1 -> ()
                           | uu____13947 -> fail lb v1))) in
            let rec check_ineq uu____13953 =
              match uu____13953 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____13960) -> true
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
                      uu____13975,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____13977,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____13984) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____13989,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____13995 -> false) in
            let uu____13998 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____14008  ->
                      match uu____14008 with
                      | (u,v1) ->
                          let uu____14013 = check_ineq (u, v1) in
                          if uu____14013
                          then true
                          else
                            ((let uu____14016 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____14016
                              then
                                let uu____14017 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____14018 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____14017
                                  uu____14018
                              else ());
                             false))) in
            if uu____13998
            then ()
            else
              ((let uu____14022 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____14022
                then
                  ((let uu____14024 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____14024);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____14030 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____14030))
                else ());
               (let uu____14036 =
                  let uu____14037 =
                    let uu____14040 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____14040) in
                  FStar_Errors.Error uu____14037 in
                raise uu____14036))
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
      let fail uu____14077 =
        match uu____14077 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____14087 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____14087
       then
         let uu____14088 = wl_to_string wl in
         let uu____14089 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____14088 uu____14089
       else ());
      (let g1 =
         let uu____14104 = solve_and_commit env wl fail in
         match uu____14104 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___183_14111 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___183_14111.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___183_14111.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___183_14111.FStar_TypeChecker_Env.implicits)
             }
         | uu____14114 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___184_14117 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___184_14117.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___184_14117.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___184_14117.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____14130 = FStar_ST.read last_proof_ns in
    match uu____14130 with
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
            let uu___185_14171 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___185_14171.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___185_14171.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___185_14171.FStar_TypeChecker_Env.implicits)
            } in
          let uu____14172 =
            let uu____14173 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____14173 in
          if uu____14172
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____14179 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____14179
                   then
                     let uu____14180 = FStar_TypeChecker_Env.get_range env in
                     let uu____14181 =
                       let uu____14182 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____14182 in
                     FStar_Errors.diag uu____14180 uu____14181
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   let uu____14185 = check_trivial vc1 in
                   match uu____14185 with
                   | FStar_TypeChecker_Common.Trivial  ->
                       FStar_Pervasives_Native.Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then
                         ((let uu____14190 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____14190
                           then
                             let uu____14191 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____14192 =
                               let uu____14193 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1
                                 "Cannot solve without SMT : %s\n"
                                 uu____14193 in
                             FStar_Errors.diag uu____14191 uu____14192
                           else ());
                          FStar_Pervasives_Native.None)
                       else
                         ((let uu____14198 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____14198
                           then
                             let uu____14199 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____14200 =
                               let uu____14201 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____14201 in
                             FStar_Errors.diag uu____14199 uu____14200
                           else ());
                          (let vcs =
                             let uu____14208 = FStar_Options.use_tactics () in
                             if uu____14208
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else
                               (let uu____14214 =
                                  let uu____14218 = FStar_Options.peek () in
                                  (env, vc2, uu____14218) in
                                [uu____14214]) in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____14239  ->
                                   match uu____14239 with
                                   | (env1,goal,opts) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify;
                                           FStar_TypeChecker_Normalize.Primops]
                                           env1 goal in
                                       let uu____14247 = check_trivial goal1 in
                                       (match uu____14247 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____14249 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____14249
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            (FStar_Options.push ();
                                             FStar_Options.set opts;
                                             maybe_update_proof_ns env1;
                                             (let uu____14256 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____14256
                                              then
                                                let uu____14257 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____14258 =
                                                  let uu____14259 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____14260 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____14259 uu____14260 in
                                                FStar_Errors.diag uu____14257
                                                  uu____14258
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
      let uu____14272 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____14272 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____14277 =
            let uu____14278 =
              let uu____14281 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____14281) in
            FStar_Errors.Error uu____14278 in
          raise uu____14277
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____14290 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____14290 with
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
        let uu____14307 = FStar_Syntax_Unionfind.find u in
        match uu____14307 with
        | FStar_Pervasives_Native.None  -> true
        | uu____14309 -> false in
      let rec until_fixpoint acc implicits =
        let uu____14322 = acc in
        match uu____14322 with
        | (out,changed) ->
            (match implicits with
             | [] ->
                 if Prims.op_Negation changed
                 then out
                 else until_fixpoint ([], false) out
             | hd1::tl1 ->
                 let uu____14368 = hd1 in
                 (match uu____14368 with
                  | (uu____14375,env,u,tm,k,r) ->
                      let uu____14381 = unresolved u in
                      if uu____14381
                      then until_fixpoint ((hd1 :: out), changed) tl1
                      else
                        (let env1 =
                           FStar_TypeChecker_Env.set_expected_typ env k in
                         let tm1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta] env1 tm in
                         (let uu____14399 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "RelCheck") in
                          if uu____14399
                          then
                            let uu____14400 =
                              FStar_Syntax_Print.uvar_to_string u in
                            let uu____14401 =
                              FStar_Syntax_Print.term_to_string tm1 in
                            let uu____14402 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print3
                              "Checking uvar %s resolved to %s at type %s\n"
                              uu____14400 uu____14401 uu____14402
                          else ());
                         (let env2 =
                            if forcelax
                            then
                              let uu___186_14405 = env1 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___186_14405.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___186_14405.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___186_14405.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___186_14405.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___186_14405.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___186_14405.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___186_14405.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___186_14405.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___186_14405.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___186_14405.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___186_14405.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___186_14405.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___186_14405.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___186_14405.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___186_14405.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___186_14405.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___186_14405.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___186_14405.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___186_14405.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___186_14405.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___186_14405.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___186_14405.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___186_14405.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___186_14405.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___186_14405.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___186_14405.FStar_TypeChecker_Env.is_native_tactic)
                              }
                            else env1 in
                          let uu____14407 =
                            env2.FStar_TypeChecker_Env.type_of
                              (let uu___187_14412 = env2 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___187_14412.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___187_14412.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___187_14412.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___187_14412.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___187_14412.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___187_14412.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___187_14412.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___187_14412.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___187_14412.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___187_14412.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___187_14412.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___187_14412.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___187_14412.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___187_14412.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___187_14412.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___187_14412.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___187_14412.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___187_14412.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___187_14412.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___187_14412.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___187_14412.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___187_14412.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___187_14412.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___187_14412.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___187_14412.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___187_14412.FStar_TypeChecker_Env.is_native_tactic)
                               }) tm1 in
                          match uu____14407 with
                          | (uu____14413,uu____14414,g1) ->
                              let g2 =
                                if env2.FStar_TypeChecker_Env.is_pattern
                                then
                                  let uu___188_14417 = g1 in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      FStar_TypeChecker_Common.Trivial;
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___188_14417.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___188_14417.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits =
                                      (uu___188_14417.FStar_TypeChecker_Env.implicits)
                                  }
                                else g1 in
                              let g' =
                                let uu____14420 =
                                  discharge_guard'
                                    (FStar_Pervasives_Native.Some
                                       (fun uu____14425  ->
                                          FStar_Syntax_Print.term_to_string
                                            tm1)) env2 g2 true in
                                match uu____14420 with
                                | FStar_Pervasives_Native.Some g3 -> g3
                                | FStar_Pervasives_Native.None  ->
                                    failwith
                                      "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                              until_fixpoint
                                ((FStar_List.append
                                    g'.FStar_TypeChecker_Env.implicits out),
                                  true) tl1)))) in
      let uu___189_14440 = g in
      let uu____14441 =
        until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___189_14440.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___189_14440.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs =
          (uu___189_14440.FStar_TypeChecker_Env.univ_ineqs);
        FStar_TypeChecker_Env.implicits = uu____14441
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
        let uu____14479 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____14479 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____14486 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____14486
      | (reason,uu____14488,uu____14489,e,t,r)::uu____14493 ->
          let uu____14507 =
            let uu____14508 =
              let uu____14511 =
                let uu____14512 = FStar_Syntax_Print.term_to_string t in
                let uu____14513 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____14512 uu____14513 in
              (uu____14511, r) in
            FStar_Errors.Error uu____14508 in
          raise uu____14507
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___190_14522 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___190_14522.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___190_14522.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___190_14522.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14543 = try_teq false env t1 t2 in
        match uu____14543 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____14546 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____14546 with
             | FStar_Pervasives_Native.Some uu____14550 -> true
             | FStar_Pervasives_Native.None  -> false)