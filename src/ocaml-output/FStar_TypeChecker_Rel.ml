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
    FStar_TypeChecker_Env.guard_t option ->
      FStar_TypeChecker_Env.guard_t option
  =
  fun x  ->
    fun g  ->
      match g with
      | None  -> g
      | Some
          {
            FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
            FStar_TypeChecker_Env.deferred = uu____61;
            FStar_TypeChecker_Env.univ_ineqs = uu____62;
            FStar_TypeChecker_Env.implicits = uu____63;_}
          -> g
      | Some g1 ->
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
                  (Some
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
          Some uu____79
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
                (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
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
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid ->
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
            ((FStar_List.append (fst g1.FStar_TypeChecker_Env.univ_ineqs)
                (fst g2.FStar_TypeChecker_Env.univ_ineqs)),
              (FStar_List.append (snd g1.FStar_TypeChecker_Env.univ_ineqs)
                 (snd g2.FStar_TypeChecker_Env.univ_ineqs)));
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
                       let uu____255 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____255
                       then f1
                       else FStar_Syntax_Util.mk_forall u (fst b) f1) us bs f in
            let uu___138_257 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___138_257.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___138_257.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___138_257.FStar_TypeChecker_Env.implicits)
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
               let uu____274 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____274
               then f1
               else
                 (let u =
                    env.FStar_TypeChecker_Env.universe_of env
                      (fst b).FStar_Syntax_Syntax.sort in
                  FStar_Syntax_Util.mk_forall u (fst b) f1)) bs f
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
            let uu___139_290 = g in
            let uu____291 =
              let uu____292 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____292 in
            {
              FStar_TypeChecker_Env.guard_f = uu____291;
              FStar_TypeChecker_Env.deferred =
                (uu___139_290.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___139_290.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___139_290.FStar_TypeChecker_Env.implicits)
            }
let new_uvar:
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.typ)
  =
  fun r  ->
    fun binders  ->
      fun k  ->
        let uv = FStar_Syntax_Unionfind.fresh () in
        match binders with
        | [] ->
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k))
                (Some (k.FStar_Syntax_Syntax.n)) r in
            (uv1, uv1)
        | uu____323 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____338 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____338 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                None r in
            let uu____350 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                (Some (k.FStar_Syntax_Syntax.n)) r in
            (uu____350, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____382 = FStar_Syntax_Util.type_u () in
        match uu____382 with
        | (t_type,u) ->
            let uu____387 =
              let uu____390 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____390 t_type in
            (match uu____387 with
             | (tt,uu____392) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of ((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
  FStar_Syntax_Syntax.term)
  | UNIV of (FStar_Syntax_Syntax.universe_uvar* FStar_Syntax_Syntax.universe)
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____416 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
      FStar_Syntax_Syntax.term)
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____444 -> false
let __proj__UNIV__item___0:
  uvi -> (FStar_Syntax_Syntax.universe_uvar* FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | UNIV _0 -> _0
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs;
  wl_deferred:
    (Prims.int* Prims.string* FStar_TypeChecker_Common.prob) Prims.list;
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
    (Prims.int* Prims.string* FStar_TypeChecker_Common.prob) Prims.list
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
  | Failed of (FStar_TypeChecker_Common.prob* Prims.string)
let uu___is_Success: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____540 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____556 -> false
let __proj__Failed__item___0:
  solution -> (FStar_TypeChecker_Common.prob* Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0
type variance =
  | COVARIANT
  | CONTRAVARIANT
  | INVARIANT
let uu___is_COVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____575 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____580 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____585 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___107_603  ->
    match uu___107_603 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____619 =
    let uu____620 = FStar_Syntax_Subst.compress t in
    uu____620.FStar_Syntax_Syntax.n in
  match uu____619 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____637 = FStar_Syntax_Print.uvar_to_string u in
      let uu____638 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____637 uu____638
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____641;
         FStar_Syntax_Syntax.pos = uu____642;
         FStar_Syntax_Syntax.vars = uu____643;_},args)
      ->
      let uu____671 = FStar_Syntax_Print.uvar_to_string u in
      let uu____672 = FStar_Syntax_Print.term_to_string ty in
      let uu____673 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" uu____671 uu____672 uu____673
  | uu____674 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___108_682  ->
      match uu___108_682 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____686 =
            let uu____688 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____689 =
              let uu____691 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____692 =
                let uu____694 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____695 =
                  let uu____697 =
                    let uu____699 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____700 =
                      let uu____702 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____703 =
                        let uu____705 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (fst p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____706 =
                          let uu____708 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____708] in
                        uu____705 :: uu____706 in
                      uu____702 :: uu____703 in
                    uu____699 :: uu____700 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____697 in
                uu____694 :: uu____695 in
              uu____691 :: uu____692 in
            uu____688 :: uu____689 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____686
      | FStar_TypeChecker_Common.CProb p ->
          let uu____713 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____714 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____713
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____714
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___109_722  ->
      match uu___109_722 with
      | UNIV (u,t) ->
          let x =
            let uu____726 = FStar_Options.hide_uvar_nums () in
            if uu____726
            then "?"
            else
              (let uu____728 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____728 FStar_Util.string_of_int) in
          let uu____729 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____729
      | TERM ((u,uu____731),t) ->
          let x =
            let uu____736 = FStar_Options.hide_uvar_nums () in
            if uu____736
            then "?"
            else
              (let uu____738 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____738 FStar_Util.string_of_int) in
          let uu____739 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____739
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____750 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____750 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____759 =
      let uu____761 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____761
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____759 (FStar_String.concat ", ")
let args_to_string args =
  let uu____781 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____789  ->
            match uu____789 with
            | (x,uu____793) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right uu____781 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____799 =
      let uu____800 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____800 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____799;
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
        let uu___140_816 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___140_816.wl_deferred);
          ctr = (uu___140_816.ctr);
          defer_ok = (uu___140_816.defer_ok);
          smt_ok;
          tcenv = (uu___140_816.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___141_846 = empty_worklist env in
  let uu____847 = FStar_List.map FStar_Pervasives.snd g in
  {
    attempting = uu____847;
    wl_deferred = (uu___141_846.wl_deferred);
    ctr = (uu___141_846.ctr);
    defer_ok = false;
    smt_ok = (uu___141_846.smt_ok);
    tcenv = (uu___141_846.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___142_862 = wl in
        {
          attempting = (uu___142_862.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___142_862.ctr);
          defer_ok = (uu___142_862.defer_ok);
          smt_ok = (uu___142_862.smt_ok);
          tcenv = (uu___142_862.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___143_876 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___143_876.wl_deferred);
        ctr = (uu___143_876.ctr);
        defer_ok = (uu___143_876.defer_ok);
        smt_ok = (uu___143_876.smt_ok);
        tcenv = (uu___143_876.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____890 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____890
         then
           let uu____891 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____891
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___110_896  ->
    match uu___110_896 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___144_915 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___144_915.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___144_915.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___144_915.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___144_915.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___144_915.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___144_915.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___144_915.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___111_940  ->
    match uu___111_940 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___112_958  ->
      match uu___112_958 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___113_962  ->
    match uu___113_962 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___114_972  ->
    match uu___114_972 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___115_983  ->
    match uu___115_983 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___116_994  ->
    match uu___116_994 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun uu___117_1006  ->
    match uu___117_1006 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___118_1018  ->
    match uu___118_1018 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___119_1028  ->
    match uu___119_1028 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____1043 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1043 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1059  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1118 = next_pid () in
  let uu____1119 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1118;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1119;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1175 = next_pid () in
  let uu____1176 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1175;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1176;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1225 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1225;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = (p_guard orig);
    FStar_TypeChecker_Common.scope = (p_scope orig);
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  }
let guard_on_element wl problem x phi =
  match problem.FStar_TypeChecker_Common.element with
  | None  ->
      let u =
        (wl.tcenv).FStar_TypeChecker_Env.universe_of wl.tcenv
          x.FStar_Syntax_Syntax.sort in
      FStar_Syntax_Util.mk_forall u x phi
  | Some e -> FStar_Syntax_Subst.subst [FStar_Syntax_Syntax.NT (x, e)] phi
let explain:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____1285 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1285
        then
          let uu____1286 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1287 = prob_to_string env d in
          let uu____1288 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1286 uu____1287 uu____1288 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1293 -> failwith "impossible" in
           let uu____1294 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1302 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1303 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1302, uu____1303)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1307 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1308 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1307, uu____1308) in
           match uu____1294 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___120_1318  ->
            match uu___120_1318 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1324 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1326),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___121_1341  ->
           match uu___121_1341 with
           | UNIV uu____1343 -> None
           | TERM ((u,uu____1347),t) ->
               let uu____1351 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1351 then Some t else None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___122_1365  ->
           match uu___122_1365 with
           | UNIV (u',t) ->
               let uu____1369 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1369 then Some t else None
           | uu____1372 -> None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1381 =
        let uu____1382 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1382 in
      FStar_Syntax_Subst.compress uu____1381
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1391 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1391
let norm_arg env t = let uu____1413 = sn env (fst t) in (uu____1413, (snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1432  ->
              match uu____1432 with
              | (x,imp) ->
                  let uu____1439 =
                    let uu___145_1440 = x in
                    let uu____1441 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___145_1440.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___145_1440.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1441
                    } in
                  (uu____1439, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1458 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1458
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1461 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1461
        | uu____1463 -> u2 in
      let uu____1464 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1464
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1580 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____1580 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1592;
               FStar_Syntax_Syntax.pos = uu____1593;
               FStar_Syntax_Syntax.vars = uu____1594;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1615 =
                 let uu____1616 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1617 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1616
                   uu____1617 in
               failwith uu____1615)
    | FStar_Syntax_Syntax.Tm_uinst uu____1627 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1654 =
             let uu____1655 = FStar_Syntax_Subst.compress t1' in
             uu____1655.FStar_Syntax_Syntax.n in
           match uu____1654 with
           | FStar_Syntax_Syntax.Tm_refine uu____1667 -> aux true t1'
           | uu____1672 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1684 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1707 =
             let uu____1708 = FStar_Syntax_Subst.compress t1' in
             uu____1708.FStar_Syntax_Syntax.n in
           match uu____1707 with
           | FStar_Syntax_Syntax.Tm_refine uu____1720 -> aux true t1'
           | uu____1725 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_app uu____1737 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1769 =
             let uu____1770 = FStar_Syntax_Subst.compress t1' in
             uu____1770.FStar_Syntax_Syntax.n in
           match uu____1769 with
           | FStar_Syntax_Syntax.Tm_refine uu____1782 -> aux true t1'
           | uu____1787 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_type uu____1799 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_constant uu____1811 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_name uu____1823 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1835 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1847 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_abs uu____1866 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1887 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_let uu____1907 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_match uu____1926 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_meta uu____1953 ->
        let uu____1958 =
          let uu____1959 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1960 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1959
            uu____1960 in
        failwith uu____1958
    | FStar_Syntax_Syntax.Tm_ascribed uu____1970 ->
        let uu____1988 =
          let uu____1989 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1990 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1989
            uu____1990 in
        failwith uu____1988
    | FStar_Syntax_Syntax.Tm_delayed uu____2000 ->
        let uu____2015 =
          let uu____2016 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2017 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2016
            uu____2017 in
        failwith uu____2015
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____2027 =
          let uu____2028 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2029 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2028
            uu____2029 in
        failwith uu____2027 in
  let uu____2039 = whnf env t1 in aux false uu____2039
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____2050 =
        let uu____2060 = empty_worklist env in
        base_and_refinement env uu____2060 t in
      FStar_All.pipe_right uu____2050 FStar_Pervasives.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____2085 = FStar_Syntax_Syntax.null_bv t in
    (uu____2085, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____2109 = base_and_refinement env wl t in
  match uu____2109 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
let force_refinement uu____2170 =
  match uu____2170 with
  | (t_base,refopt) ->
      let uu____2184 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base in
      (match uu____2184 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___123_2210  ->
      match uu___123_2210 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2214 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2215 =
            let uu____2216 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____2216 in
          let uu____2217 =
            let uu____2218 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____2218 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2214 uu____2215
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2217
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2222 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2223 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____2224 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2222 uu____2223
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2224
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2229 =
      let uu____2231 =
        let uu____2233 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2243  ->
                  match uu____2243 with | (uu____2247,uu____2248,x) -> x)) in
        FStar_List.append wl.attempting uu____2233 in
      FStar_List.map (wl_prob_to_string wl) uu____2231 in
    FStar_All.pipe_right uu____2229 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2269 =
          let uu____2279 =
            let uu____2280 = FStar_Syntax_Subst.compress k in
            uu____2280.FStar_Syntax_Syntax.n in
          match uu____2279 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2325 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2325)
              else
                (let uu____2339 = FStar_Syntax_Util.abs_formals t in
                 match uu____2339 with
                 | (ys',t1,uu____2355) ->
                     let uu____2358 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2358))
          | uu____2379 ->
              let uu____2380 =
                let uu____2386 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____2386) in
              ((ys, t), uu____2380) in
        match uu____2269 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Syntax_Util.mk_residual_comp
                      FStar_Syntax_Const.effect_Tot_lid None []))
            else
              (let c1 =
                 let uu____2438 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2438 c in
               FStar_Syntax_Util.abs ys1 t1
                 (Some (FStar_Syntax_Util.residual_comp_of_comp c1)))
let solve_prob':
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term option ->
        uvi Prims.list -> worklist -> worklist
  =
  fun resolve_ok  ->
    fun prob  ->
      fun logical_guard  ->
        fun uvis  ->
          fun wl  ->
            let phi =
              match logical_guard with
              | None  -> FStar_Syntax_Util.t_true
              | Some phi -> phi in
            let uu____2466 = p_guard prob in
            match uu____2466 with
            | (uu____2469,uv) ->
                ((let uu____2472 =
                    let uu____2473 = FStar_Syntax_Subst.compress uv in
                    uu____2473.FStar_Syntax_Syntax.n in
                  match uu____2472 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2493 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2493
                        then
                          let uu____2494 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2495 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2496 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2494
                            uu____2495 uu____2496
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2498 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___146_2501 = wl in
                  {
                    attempting = (uu___146_2501.attempting);
                    wl_deferred = (uu___146_2501.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___146_2501.defer_ok);
                    smt_ok = (uu___146_2501.smt_ok);
                    tcenv = (uu___146_2501.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2517 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2517
         then
           let uu____2518 = FStar_Util.string_of_int pid in
           let uu____2519 =
             let uu____2520 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2520 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2518 uu____2519
         else ());
        commit sol;
        (let uu___147_2525 = wl in
         {
           attempting = (uu___147_2525.attempting);
           wl_deferred = (uu___147_2525.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___147_2525.defer_ok);
           smt_ok = (uu___147_2525.smt_ok);
           tcenv = (uu___147_2525.tcenv)
         })
let solve_prob:
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term option -> uvi Prims.list -> worklist -> worklist
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          let conj_guard1 t g =
            match (t, g) with
            | (uu____2558,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2566 = FStar_Syntax_Util.mk_conj t1 f in
                Some uu____2566 in
          (let uu____2572 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2572
           then
             let uu____2573 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2574 =
               let uu____2575 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2575 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2573 uu____2574
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2604 =
    let uu____2608 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2608 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2604
    (FStar_Util.for_some
       (fun uu____2625  ->
          match uu____2625 with
          | (uv,uu____2629) -> FStar_Syntax_Unionfind.equiv uv (fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2668 = occurs wl uk t in Prims.op_Negation uu____2668 in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2673 =
         let uu____2674 = FStar_Syntax_Print.uvar_to_string (fst uk) in
         let uu____2675 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2674 uu____2675 in
       Some uu____2673) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2730 = occurs_check env wl uk t in
  match uu____2730 with
  | (occurs_ok,msg) ->
      let uu____2747 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2747, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2815 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2839  ->
            fun uu____2840  ->
              match (uu____2839, uu____2840) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2883 =
                    let uu____2884 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2884 in
                  if uu____2883
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2898 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2898
                     then
                       let uu____2905 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____2905)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2815 with | (isect,uu____2927) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2984  ->
          fun uu____2985  ->
            match (uu____2984, uu____2985) with
            | ((a,uu____2995),(b,uu____2997)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____3046 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____3052  ->
                match uu____3052 with
                | (b,uu____3056) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____3046 then None else Some (a, (snd hd1))
  | uu____3065 -> None
let rec pat_vars:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_Syntax_Syntax.binders option
  =
  fun env  ->
    fun seen  ->
      fun args  ->
        match args with
        | [] -> Some (FStar_List.rev seen)
        | hd1::rest ->
            let uu____3111 = pat_var_opt env seen hd1 in
            (match uu____3111 with
             | None  ->
                 ((let uu____3119 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____3119
                   then
                     let uu____3120 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____3120
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3133 =
      let uu____3134 = FStar_Syntax_Subst.compress t in
      uu____3134.FStar_Syntax_Syntax.n in
    match uu____3133 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3137 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3146;
           FStar_Syntax_Syntax.tk = uu____3147;
           FStar_Syntax_Syntax.pos = uu____3148;
           FStar_Syntax_Syntax.vars = uu____3149;_},uu____3150)
        -> true
    | uu____3173 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3237;
         FStar_Syntax_Syntax.pos = uu____3238;
         FStar_Syntax_Syntax.vars = uu____3239;_},args)
      -> (t, uv, k, args)
  | uu____3280 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____3337 = destruct_flex_t t in
  match uu____3337 with
  | (t1,uv,k,args) ->
      let uu____3405 = pat_vars env [] args in
      (match uu____3405 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3461 -> ((t1, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth option*
  FStar_Syntax_Syntax.delta_depth option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3511 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth option* FStar_Syntax_Syntax.delta_depth
      option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3536 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3541 -> false
let head_match: match_result -> match_result =
  fun uu___124_3545  ->
    match uu___124_3545 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3554 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3569 ->
          let uu____3570 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3570 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3580 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3596 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3602 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> None
      | FStar_Syntax_Syntax.Tm_bvar uu____3618 -> None
      | FStar_Syntax_Syntax.Tm_name uu____3619 -> None
      | FStar_Syntax_Syntax.Tm_uvar uu____3620 -> None
      | FStar_Syntax_Syntax.Tm_let uu____3629 -> None
      | FStar_Syntax_Syntax.Tm_match uu____3637 -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3654) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3660,uu____3661) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3691) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3706;
             FStar_Syntax_Syntax.index = uu____3707;
             FStar_Syntax_Syntax.sort = t2;_},uu____3709)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3716 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3717 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3718 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3726 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3737 = fv_delta_depth env fv in Some uu____3737
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
            else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____3759 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3759
            then FullMatch
            else
              (let uu____3761 =
                 let uu____3766 =
                   let uu____3768 = fv_delta_depth env f in Some uu____3768 in
                 let uu____3769 =
                   let uu____3771 = fv_delta_depth env g in Some uu____3771 in
                 (uu____3766, uu____3769) in
               MisMatch uu____3761)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3775),FStar_Syntax_Syntax.Tm_uinst (g,uu____3777)) ->
            let uu____3786 = head_matches env f g in
            FStar_All.pipe_right uu____3786 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3793),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3795)) ->
            let uu____3820 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____3820 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3825),FStar_Syntax_Syntax.Tm_refine (y,uu____3827)) ->
            let uu____3836 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3836 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3838),uu____3839) ->
            let uu____3844 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3844 head_match
        | (uu____3845,FStar_Syntax_Syntax.Tm_refine (x,uu____3847)) ->
            let uu____3852 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3852 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3853,FStar_Syntax_Syntax.Tm_type
           uu____3854) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3855,FStar_Syntax_Syntax.Tm_arrow uu____3856) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3872),FStar_Syntax_Syntax.Tm_app (head',uu____3874))
            ->
            let uu____3903 = head_matches env head1 head' in
            FStar_All.pipe_right uu____3903 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3905),uu____3906) ->
            let uu____3921 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____3921 head_match
        | (uu____3922,FStar_Syntax_Syntax.Tm_app (head1,uu____3924)) ->
            let uu____3939 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____3939 head_match
        | uu____3940 ->
            let uu____3943 =
              let uu____3948 = delta_depth_of_term env t11 in
              let uu____3950 = delta_depth_of_term env t21 in
              (uu____3948, uu____3950) in
            MisMatch uu____3943
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3991 = FStar_Syntax_Util.head_and_args t in
    match uu____3991 with
    | (head1,uu____4003) ->
        let uu____4018 =
          let uu____4019 = FStar_Syntax_Util.un_uinst head1 in
          uu____4019.FStar_Syntax_Syntax.n in
        (match uu____4018 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____4024 =
               let uu____4025 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____4025 FStar_Option.isSome in
             if uu____4024
             then
               let uu____4039 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____4039 (fun _0_45  -> Some _0_45)
             else None
         | uu____4042 -> None) in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None)) in
  let fail r = (r, None) in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21 in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),uu____4110) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4120 =
             let uu____4125 = maybe_inline t11 in
             let uu____4127 = maybe_inline t21 in (uu____4125, uu____4127) in
           match uu____4120 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (uu____4148,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4158 =
             let uu____4163 = maybe_inline t11 in
             let uu____4165 = maybe_inline t21 in (uu____4163, uu____4165) in
           match uu____4158 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____4190 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____4190 with
         | None  -> fail r
         | Some d ->
             let t12 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d;
                 FStar_TypeChecker_Normalize.WHNF] env wl t11 in
             let t22 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) ->
        let d1_greater_than_d2 =
          FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
        let uu____4205 =
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
             let uu____4213 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____4213)) in
        (match uu____4205 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4221 -> fail r
    | uu____4226 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4256 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4288 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4306 = FStar_Syntax_Util.type_u () in
      match uu____4306 with
      | (t,uu____4310) ->
          let uu____4311 = new_uvar r binders t in fst uu____4311
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4322 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____4322 FStar_Pervasives.fst
let rec decompose:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      ((tc Prims.list -> FStar_Syntax_Syntax.term)*
        (FStar_Syntax_Syntax.term -> Prims.bool)* (FStar_Syntax_Syntax.binder
        option* variance* tc) Prims.list)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let matches t' =
        let uu____4366 = head_matches env t1 t' in
        match uu____4366 with
        | MisMatch uu____4367 -> false
        | uu____4372 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4432,imp),T (t2,uu____4435)) -> (t2, imp)
                     | uu____4452 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4492  ->
                    match uu____4492 with
                    | (t2,uu____4500) ->
                        (None, INVARIANT, (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____4530 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____4530 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4583))::tcs2) ->
                       aux
                         (((let uu___148_4605 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_4605.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_4605.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4615 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___125_4646 =
                 match uu___125_4646 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4709 = decompose1 [] bs1 in
               (rebuild, matches, uu____4709))
      | uu____4737 ->
          let rebuild uu___126_4742 =
            match uu___126_4742 with
            | [] -> t1
            | uu____4744 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___127_4764  ->
    match uu___127_4764 with
    | T (t,uu____4766) -> t
    | uu____4775 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___128_4779  ->
    match uu___128_4779 with
    | T (t,uu____4781) -> FStar_Syntax_Syntax.as_arg t
    | uu____4790 -> failwith "Impossible"
let imitation_sub_probs:
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.args ->
          (FStar_Syntax_Syntax.binder option* variance* tc) Prims.list ->
            (FStar_TypeChecker_Common.prob Prims.list* tc Prims.list*
              FStar_Syntax_Syntax.formula)
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
              | (uu____4864,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4883 = new_uvar r scope1 k in
                  (match uu____4883 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4895 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args)) None r in
                       let uu____4910 =
                         let uu____4911 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____4911 in
                       ((T (gi_xs, mk_kind)), uu____4910))
              | (uu____4920,uu____4921,C uu____4922) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____5009 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____5020;
                         FStar_Syntax_Syntax.pos = uu____5021;
                         FStar_Syntax_Syntax.vars = uu____5022;_})
                        ->
                        let uu____5037 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____5037 with
                         | (T (gi_xs,uu____5053),prob) ->
                             let uu____5063 =
                               let uu____5064 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____5064 in
                             (uu____5063, [prob])
                         | uu____5066 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____5076;
                         FStar_Syntax_Syntax.pos = uu____5077;
                         FStar_Syntax_Syntax.vars = uu____5078;_})
                        ->
                        let uu____5093 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____5093 with
                         | (T (gi_xs,uu____5109),prob) ->
                             let uu____5119 =
                               let uu____5120 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____5120 in
                             (uu____5119, [prob])
                         | uu____5122 -> failwith "impossible")
                    | (uu____5128,uu____5129,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____5131;
                         FStar_Syntax_Syntax.pos = uu____5132;
                         FStar_Syntax_Syntax.vars = uu____5133;_})
                        ->
                        let components =
                          FStar_All.pipe_right
                            c.FStar_Syntax_Syntax.effect_args
                            (FStar_List.map
                               (fun t  ->
                                  (None, INVARIANT,
                                    (T ((fst t), generic_kind))))) in
                        let components1 =
                          (None, COVARIANT,
                            (T
                               ((c.FStar_Syntax_Syntax.result_typ),
                                 kind_type)))
                          :: components in
                        let uu____5207 =
                          let uu____5212 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____5212 FStar_List.unzip in
                        (match uu____5207 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5241 =
                                 let uu____5242 =
                                   let uu____5245 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____5245 un_T in
                                 let uu____5246 =
                                   let uu____5252 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____5252
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5242;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5246;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5241 in
                             ((C gi_xs), sub_probs))
                    | uu____5257 ->
                        let uu____5264 = sub_prob scope1 args q in
                        (match uu____5264 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____5009 with
                   | (tc,probs) ->
                       let uu____5282 =
                         match q with
                         | (Some b,uu____5308,uu____5309) ->
                             let uu____5317 =
                               let uu____5321 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____5321 :: args in
                             ((Some b), (b :: scope1), uu____5317)
                         | uu____5339 -> (None, scope1, args) in
                       (match uu____5282 with
                        | (bopt,scope2,args1) ->
                            let uu____5382 = aux scope2 args1 qs2 in
                            (match uu____5382 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____5403 =
                                         let uu____5405 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         f :: uu____5405 in
                                       FStar_Syntax_Util.mk_conj_l uu____5403
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (fst b).FStar_Syntax_Syntax.sort in
                                       let uu____5418 =
                                         let uu____5420 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (fst b) f in
                                         let uu____5421 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         uu____5420 :: uu____5421 in
                                       FStar_Syntax_Util.mk_conj_l uu____5418 in
                                 ((FStar_List.append probs sub_probs), (tc ::
                                   tcs), f1)))) in
            aux scope ps qs
type flex_t =
  (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.uvar*
    FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.args)
type im_or_proj_t =
  (((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
    FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)*
    FStar_Syntax_Syntax.arg Prims.list*
    ((tc Prims.list -> FStar_Syntax_Syntax.typ)*
    (FStar_Syntax_Syntax.typ -> Prims.bool)* (FStar_Syntax_Syntax.binder
    option* variance* tc) Prims.list))
let rigid_rigid: Prims.int = Prims.parse_int "0"
let flex_rigid_eq: Prims.int = Prims.parse_int "1"
let flex_refine_inner: Prims.int = Prims.parse_int "2"
let flex_refine: Prims.int = Prims.parse_int "3"
let flex_rigid: Prims.int = Prims.parse_int "4"
let rigid_flex: Prims.int = Prims.parse_int "5"
let refine_flex: Prims.int = Prims.parse_int "6"
let flex_flex: Prims.int = Prims.parse_int "7"
let compress_tprob wl p =
  let uu___149_5477 = p in
  let uu____5480 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____5481 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___149_5477.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5480;
    FStar_TypeChecker_Common.relation =
      (uu___149_5477.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5481;
    FStar_TypeChecker_Common.element =
      (uu___149_5477.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___149_5477.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___149_5477.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___149_5477.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___149_5477.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___149_5477.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5493 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____5493
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____5498 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5514 = compress_prob wl pr in
        FStar_All.pipe_right uu____5514 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5520 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____5520 with
           | (lh,uu____5533) ->
               let uu____5548 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____5548 with
                | (rh,uu____5561) ->
                    let uu____5576 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5585,FStar_Syntax_Syntax.Tm_uvar uu____5586)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5605,uu____5606)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5617,FStar_Syntax_Syntax.Tm_uvar uu____5618)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5629,uu____5630)
                          ->
                          let uu____5639 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5639 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5679 ->
                                    let rank =
                                      let uu____5686 = is_top_level_prob prob in
                                      if uu____5686
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5688 =
                                      let uu___150_5691 = tp in
                                      let uu____5694 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___150_5691.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___150_5691.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___150_5691.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5694;
                                        FStar_TypeChecker_Common.element =
                                          (uu___150_5691.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___150_5691.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___150_5691.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___150_5691.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___150_5691.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___150_5691.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5688)))
                      | (uu____5704,FStar_Syntax_Syntax.Tm_uvar uu____5705)
                          ->
                          let uu____5714 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5714 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5754 ->
                                    let uu____5760 =
                                      let uu___151_5765 = tp in
                                      let uu____5768 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___151_5765.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5768;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___151_5765.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___151_5765.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___151_5765.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___151_5765.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___151_5765.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___151_5765.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___151_5765.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___151_5765.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5760)))
                      | (uu____5784,uu____5785) -> (rigid_rigid, tp) in
                    (match uu____5576 with
                     | (rank,tp1) ->
                         let uu____5796 =
                           FStar_All.pipe_right
                             (let uu___152_5799 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___152_5799.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___152_5799.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___152_5799.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___152_5799.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___152_5799.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___152_5799.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___152_5799.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___152_5799.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___152_5799.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50) in
                         (rank, uu____5796))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5805 =
            FStar_All.pipe_right
              (let uu___153_5808 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___153_5808.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___153_5808.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___153_5808.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___153_5808.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___153_5808.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___153_5808.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___153_5808.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___153_5808.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___153_5808.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51) in
          (rigid_rigid, uu____5805)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob option* FStar_TypeChecker_Common.prob
      Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____5841 probs =
      match uu____5841 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5871 = rank wl hd1 in
               (match uu____5871 with
                | (rank1,hd2) ->
                    if rank1 <= flex_rigid_eq
                    then
                      (match min1 with
                       | None  ->
                           ((Some hd2), (FStar_List.append out tl1), rank1)
                       | Some m ->
                           ((Some hd2), (FStar_List.append out (m :: tl1)),
                             rank1))
                    else
                      if rank1 < min_rank
                      then
                        (match min1 with
                         | None  -> aux (rank1, (Some hd2), out) tl1
                         | Some m -> aux (rank1, (Some hd2), (m :: out)) tl1)
                      else aux (min_rank, min1, (hd2 :: out)) tl1)) in
    aux ((flex_flex + (Prims.parse_int "1")), None, []) wl.attempting
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
    match projectee with | UDeferred _0 -> true | uu____5942 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5956 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5970 -> false
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
                        let uu____6008 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____6008 with
                        | (k,uu____6012) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____6016 -> false)))
            | uu____6017 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____6064 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____6064 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____6067 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____6073 =
                     let uu____6074 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____6075 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____6074
                       uu____6075 in
                   UFailed uu____6073)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____6091 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____6091 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____6109 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____6109 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____6112 ->
                let uu____6115 =
                  let uu____6116 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____6117 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____6116
                    uu____6117 msg in
                UFailed uu____6115 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____6118,uu____6119) ->
              let uu____6120 =
                let uu____6121 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6122 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6121 uu____6122 in
              failwith uu____6120
          | (FStar_Syntax_Syntax.U_unknown ,uu____6123) ->
              let uu____6124 =
                let uu____6125 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6126 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6125 uu____6126 in
              failwith uu____6124
          | (uu____6127,FStar_Syntax_Syntax.U_bvar uu____6128) ->
              let uu____6129 =
                let uu____6130 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6131 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6130 uu____6131 in
              failwith uu____6129
          | (uu____6132,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____6133 =
                let uu____6134 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6135 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6134 uu____6135 in
              failwith uu____6133
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____6147 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____6147
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____6157 = occurs_univ v1 u3 in
              if uu____6157
              then
                let uu____6158 =
                  let uu____6159 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6160 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6159 uu____6160 in
                try_umax_components u11 u21 uu____6158
              else
                (let uu____6162 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6162)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____6170 = occurs_univ v1 u3 in
              if uu____6170
              then
                let uu____6171 =
                  let uu____6172 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6173 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6172 uu____6173 in
                try_umax_components u11 u21 uu____6171
              else
                (let uu____6175 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6175)
          | (FStar_Syntax_Syntax.U_max uu____6178,uu____6179) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6184 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6184
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____6186,FStar_Syntax_Syntax.U_max uu____6187) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6192 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6192
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6194,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6195,FStar_Syntax_Syntax.U_name
             uu____6196) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6197) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6198) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6199,FStar_Syntax_Syntax.U_succ
             uu____6200) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6201,FStar_Syntax_Syntax.U_zero
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
  let uu____6271 = bc1 in
  match uu____6271 with
  | (bs1,mk_cod1) ->
      let uu____6296 = bc2 in
      (match uu____6296 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6343 = FStar_Util.first_N n1 bs in
             match uu____6343 with
             | (bs3,rest) ->
                 let uu____6357 = mk_cod rest in (bs3, uu____6357) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____6381 =
               let uu____6385 = mk_cod1 [] in (bs1, uu____6385) in
             let uu____6387 =
               let uu____6391 = mk_cod2 [] in (bs2, uu____6391) in
             (uu____6381, uu____6387)
           else
             if l1 > l2
             then
               (let uu____6418 = curry l2 bs1 mk_cod1 in
                let uu____6428 =
                  let uu____6432 = mk_cod2 [] in (bs2, uu____6432) in
                (uu____6418, uu____6428))
             else
               (let uu____6441 =
                  let uu____6445 = mk_cod1 [] in (bs1, uu____6445) in
                let uu____6447 = curry l1 bs2 mk_cod2 in
                (uu____6441, uu____6447)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6554 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____6554
       then
         let uu____6555 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6555
       else ());
      (let uu____6557 = next_prob probs in
       match uu____6557 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___154_6570 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___154_6570.wl_deferred);
               ctr = (uu___154_6570.ctr);
               defer_ok = (uu___154_6570.defer_ok);
               smt_ok = (uu___154_6570.smt_ok);
               tcenv = (uu___154_6570.tcenv)
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
                  let uu____6577 = solve_flex_rigid_join env tp probs1 in
                  (match uu____6577 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6581 = solve_rigid_flex_meet env tp probs1 in
                     match uu____6581 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____6585,uu____6586) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6595 ->
                let uu____6600 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6628  ->
                          match uu____6628 with
                          | (c,uu____6633,uu____6634) -> c < probs.ctr)) in
                (match uu____6600 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6656 =
                            FStar_List.map
                              (fun uu____6662  ->
                                 match uu____6662 with
                                 | (uu____6668,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____6656
                      | uu____6671 ->
                          let uu____6676 =
                            let uu___155_6677 = probs in
                            let uu____6678 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6687  ->
                                      match uu____6687 with
                                      | (uu____6691,uu____6692,y) -> y)) in
                            {
                              attempting = uu____6678;
                              wl_deferred = rest;
                              ctr = (uu___155_6677.ctr);
                              defer_ok = (uu___155_6677.defer_ok);
                              smt_ok = (uu___155_6677.smt_ok);
                              tcenv = (uu___155_6677.tcenv)
                            } in
                          solve env uu____6676))))
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
            let uu____6699 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____6699 with
            | USolved wl1 ->
                let uu____6701 = solve_prob orig None [] wl1 in
                solve env uu____6701
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
                  let uu____6735 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6735 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6738 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6746;
                  FStar_Syntax_Syntax.pos = uu____6747;
                  FStar_Syntax_Syntax.vars = uu____6748;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6751;
                  FStar_Syntax_Syntax.pos = uu____6752;
                  FStar_Syntax_Syntax.vars = uu____6753;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6765,uu____6766) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6771,FStar_Syntax_Syntax.Tm_uinst uu____6772) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6777 -> USolved wl
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
            ((let uu____6785 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6785
              then
                let uu____6786 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6786 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6794 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6794
         then
           let uu____6795 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6795
         else ());
        (let uu____6797 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6797 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6839 = head_matches_delta env () t1 t2 in
               match uu____6839 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6861 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6887 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6896 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____6897 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____6896, uu____6897)
                          | None  ->
                              let uu____6900 = FStar_Syntax_Subst.compress t1 in
                              let uu____6901 = FStar_Syntax_Subst.compress t2 in
                              (uu____6900, uu____6901) in
                        (match uu____6887 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6923 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____6923 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6946 =
                                    let uu____6952 =
                                      let uu____6955 =
                                        let uu____6958 =
                                          let uu____6959 =
                                            let uu____6964 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____6964) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6959 in
                                        FStar_Syntax_Syntax.mk uu____6958 in
                                      uu____6955 None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____6977 =
                                      let uu____6979 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____6979] in
                                    (uu____6952, uu____6977) in
                                  Some uu____6946
                              | (uu____6988,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6990)) ->
                                  let uu____6995 =
                                    let uu____6999 =
                                      let uu____7001 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____7001] in
                                    (t11, uu____6999) in
                                  Some uu____6995
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____7007),uu____7008) ->
                                  let uu____7013 =
                                    let uu____7017 =
                                      let uu____7019 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____7019] in
                                    (t21, uu____7017) in
                                  Some uu____7013
                              | uu____7024 ->
                                  let uu____7027 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____7027 with
                                   | (head1,uu____7042) ->
                                       let uu____7057 =
                                         let uu____7058 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____7058.FStar_Syntax_Syntax.n in
                                       (match uu____7057 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____7065;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____7067;_}
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
                                        | uu____7076 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7085) ->
                  let uu____7098 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___129_7107  ->
                            match uu___129_7107 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____7112 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____7112 with
                                      | (u',uu____7123) ->
                                          let uu____7138 =
                                            let uu____7139 = whnf env u' in
                                            uu____7139.FStar_Syntax_Syntax.n in
                                          (match uu____7138 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____7143) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____7156 -> false))
                                 | uu____7157 -> false)
                            | uu____7159 -> false)) in
                  (match uu____7098 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____7180 tps =
                         match uu____7180 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7207 =
                                    let uu____7212 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____7212 in
                                  (match uu____7207 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____7231 -> None) in
                       let uu____7236 =
                         let uu____7241 =
                           let uu____7245 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____7245, []) in
                         make_lower_bound uu____7241 lower_bounds in
                       (match uu____7236 with
                        | None  ->
                            ((let uu____7252 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7252
                              then
                                FStar_Util.print_string "No lower bounds\n"
                              else ());
                             None)
                        | Some (lhs_bound,sub_probs) ->
                            let eq_prob =
                              new_problem env lhs_bound
                                FStar_TypeChecker_Common.EQ
                                tp.FStar_TypeChecker_Common.rhs None
                                tp.FStar_TypeChecker_Common.loc
                                "meeting refinements" in
                            ((let uu____7265 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7265
                              then
                                let wl' =
                                  let uu___156_7267 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___156_7267.wl_deferred);
                                    ctr = (uu___156_7267.ctr);
                                    defer_ok = (uu___156_7267.defer_ok);
                                    smt_ok = (uu___156_7267.smt_ok);
                                    tcenv = (uu___156_7267.tcenv)
                                  } in
                                let uu____7268 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7268
                              else ());
                             (let uu____7270 =
                                solve_t env eq_prob
                                  (let uu___157_7271 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___157_7271.wl_deferred);
                                     ctr = (uu___157_7271.ctr);
                                     defer_ok = (uu___157_7271.defer_ok);
                                     smt_ok = (uu___157_7271.smt_ok);
                                     tcenv = (uu___157_7271.tcenv)
                                   }) in
                              match uu____7270 with
                              | Success uu____7273 ->
                                  let wl1 =
                                    let uu___158_7275 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___158_7275.wl_deferred);
                                      ctr = (uu___158_7275.ctr);
                                      defer_ok = (uu___158_7275.defer_ok);
                                      smt_ok = (uu___158_7275.smt_ok);
                                      tcenv = (uu___158_7275.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1 in
                                  let uu____7277 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds in
                                  Some wl2
                              | uu____7280 -> None))))
              | uu____7281 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7288 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____7288
         then
           let uu____7289 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7289
         else ());
        (let uu____7291 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____7291 with
         | (u,args) ->
             let uu____7318 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____7318 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____7349 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____7349 with
                    | (h1,args1) ->
                        let uu____7377 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____7377 with
                         | (h2,uu____7390) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7409 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____7409
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7424 =
                                          let uu____7426 =
                                            let uu____7427 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____7427 in
                                          [uu____7426] in
                                        Some uu____7424))
                                  else None
                              | (FStar_Syntax_Syntax.Tm_name
                                 a,FStar_Syntax_Syntax.Tm_name b) ->
                                  if FStar_Syntax_Syntax.bv_eq a b
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7451 =
                                          let uu____7453 =
                                            let uu____7454 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____7454 in
                                          [uu____7453] in
                                        Some uu____7451))
                                  else None
                              | uu____7462 -> None)) in
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
                         | None  -> None
                         | Some m1 ->
                             let x1 = FStar_Syntax_Syntax.freshen_bv x in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x1)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let uu____7528 =
                               let uu____7534 =
                                 let uu____7537 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____7537 in
                               (uu____7534, m1) in
                             Some uu____7528)
                    | (uu____7546,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7548)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7580),uu____7581) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____7612 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7646) ->
                       let uu____7659 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___130_7668  ->
                                 match uu___130_7668 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____7673 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____7673 with
                                           | (u',uu____7684) ->
                                               let uu____7699 =
                                                 let uu____7700 = whnf env u' in
                                                 uu____7700.FStar_Syntax_Syntax.n in
                                               (match uu____7699 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7704) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____7717 -> false))
                                      | uu____7718 -> false)
                                 | uu____7720 -> false)) in
                       (match uu____7659 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7745 tps =
                              match uu____7745 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7786 =
                                         let uu____7793 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7793 in
                                       (match uu____7786 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7828 -> None) in
                            let uu____7835 =
                              let uu____7842 =
                                let uu____7848 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7848, []) in
                              make_upper_bound uu____7842 upper_bounds in
                            (match uu____7835 with
                             | None  ->
                                 ((let uu____7857 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7857
                                   then
                                     FStar_Util.print_string
                                       "No upper bounds\n"
                                   else ());
                                  None)
                             | Some (rhs_bound,sub_probs) ->
                                 let eq_prob =
                                   new_problem env
                                     tp.FStar_TypeChecker_Common.lhs
                                     FStar_TypeChecker_Common.EQ rhs_bound
                                     None tp.FStar_TypeChecker_Common.loc
                                     "joining refinements" in
                                 ((let uu____7876 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7876
                                   then
                                     let wl' =
                                       let uu___159_7878 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___159_7878.wl_deferred);
                                         ctr = (uu___159_7878.ctr);
                                         defer_ok = (uu___159_7878.defer_ok);
                                         smt_ok = (uu___159_7878.smt_ok);
                                         tcenv = (uu___159_7878.tcenv)
                                       } in
                                     let uu____7879 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7879
                                   else ());
                                  (let uu____7881 =
                                     solve_t env eq_prob
                                       (let uu___160_7882 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___160_7882.wl_deferred);
                                          ctr = (uu___160_7882.ctr);
                                          defer_ok = (uu___160_7882.defer_ok);
                                          smt_ok = (uu___160_7882.smt_ok);
                                          tcenv = (uu___160_7882.tcenv)
                                        }) in
                                   match uu____7881 with
                                   | Success uu____7884 ->
                                       let wl1 =
                                         let uu___161_7886 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___161_7886.wl_deferred);
                                           ctr = (uu___161_7886.ctr);
                                           defer_ok =
                                             (uu___161_7886.defer_ok);
                                           smt_ok = (uu___161_7886.smt_ok);
                                           tcenv = (uu___161_7886.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1 in
                                       let uu____7888 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds in
                                       Some wl2
                                   | uu____7891 -> None))))
                   | uu____7892 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____7957 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____7957
                      then
                        let uu____7958 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7958
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___162_7990 = hd1 in
                      let uu____7991 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___162_7990.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___162_7990.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7991
                      } in
                    let hd21 =
                      let uu___163_7995 = hd2 in
                      let uu____7996 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___163_7995.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___163_7995.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7996
                      } in
                    let prob =
                      let uu____8000 =
                        let uu____8003 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____8003 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____8000 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____8011 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____8011 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____8014 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____8014 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____8032 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives.fst in
                           let uu____8035 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____8032 uu____8035 in
                         ((let uu____8041 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____8041
                           then
                             let uu____8042 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____8043 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____8042 uu____8043
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____8058 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____8064 = aux scope env [] bs1 bs2 in
              match uu____8064 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____8080 = compress_tprob wl problem in
        solve_t' env uu____8080 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____8113 = head_matches_delta env1 wl1 t1 t2 in
          match uu____8113 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____8130,uu____8131) ->
                   let may_relate head3 =
                     let uu____8146 =
                       let uu____8147 = FStar_Syntax_Util.un_uinst head3 in
                       uu____8147.FStar_Syntax_Syntax.n in
                     match uu____8146 with
                     | FStar_Syntax_Syntax.Tm_name uu____8150 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____8151 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____8168 -> false in
                   let uu____8169 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____8169
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
                            | Some t ->
                                FStar_Syntax_Util.mk_has_type t11 t t21
                            | None  ->
                                let x = FStar_Syntax_Syntax.new_bv None t11 in
                                let u_x =
                                  env1.FStar_TypeChecker_Env.universe_of env1
                                    t11 in
                                let uu____8186 =
                                  let uu____8187 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____8187 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____8186 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____8189 = solve_prob orig (Some guard) [] wl1 in
                     solve env1 uu____8189
                   else
                     (let uu____8191 =
                        let uu____8192 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____8193 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____8192 uu____8193 in
                      giveup env1 uu____8191 orig)
               | (uu____8194,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___164_8202 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___164_8202.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___164_8202.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___164_8202.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___164_8202.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___164_8202.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___164_8202.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___164_8202.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___164_8202.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____8203,None ) ->
                   ((let uu____8210 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8210
                     then
                       let uu____8211 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____8212 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____8213 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____8214 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____8211
                         uu____8212 uu____8213 uu____8214
                     else ());
                    (let uu____8216 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____8216 with
                     | (head11,args1) ->
                         let uu____8242 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____8242 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8287 =
                                  let uu____8288 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____8289 = args_to_string args1 in
                                  let uu____8290 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____8291 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8288 uu____8289 uu____8290
                                    uu____8291 in
                                giveup env1 uu____8287 orig
                              else
                                (let uu____8293 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8298 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____8298 = FStar_Syntax_Util.Equal) in
                                 if uu____8293
                                 then
                                   let uu____8299 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____8299 with
                                   | USolved wl2 ->
                                       let uu____8301 =
                                         solve_prob orig None [] wl2 in
                                       solve env1 uu____8301
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8305 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____8305 with
                                    | (base1,refinement1) ->
                                        let uu____8331 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____8331 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____8385 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____8385 with
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
                                                           (fun uu____8395 
                                                              ->
                                                              fun uu____8396 
                                                                ->
                                                                match 
                                                                  (uu____8395,
                                                                    uu____8396)
                                                                with
                                                                | ((a,uu____8406),
                                                                   (a',uu____8408))
                                                                    ->
                                                                    let uu____8413
                                                                    =
                                                                    mk_problem
                                                                    (p_scope
                                                                    orig)
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a' None
                                                                    "index" in
                                                                    FStar_All.pipe_left
                                                                    (fun
                                                                    _0_56  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_56)
                                                                    uu____8413)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____8419 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8419 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8423 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___165_8456 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___165_8456.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___165_8456.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___165_8456.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___165_8456.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___165_8456.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___165_8456.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___165_8456.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___165_8456.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____8476 = p in
          match uu____8476 with
          | (((u,k),xs,c),ps,(h,uu____8487,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8536 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____8536 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8550 = h gs_xs in
                     let uu____8551 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> Some _0_57) in
                     FStar_Syntax_Util.abs xs1 uu____8550 uu____8551 in
                   ((let uu____8555 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8555
                     then
                       let uu____8556 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____8557 = FStar_Syntax_Print.comp_to_string c in
                       let uu____8558 = FStar_Syntax_Print.term_to_string im in
                       let uu____8559 = FStar_Syntax_Print.tag_of_term im in
                       let uu____8560 =
                         let uu____8561 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____8561
                           (FStar_String.concat ", ") in
                       let uu____8564 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8556 uu____8557 uu____8558 uu____8559
                         uu____8560 uu____8564
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___131_8582 =
          match uu___131_8582 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____8611 = p in
          match uu____8611 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8669 = FStar_List.nth ps i in
              (match uu____8669 with
               | (pi,uu____8672) ->
                   let uu____8677 = FStar_List.nth xs i in
                   (match uu____8677 with
                    | (xi,uu____8684) ->
                        let rec gs k =
                          let uu____8693 = FStar_Syntax_Util.arrow_formals k in
                          match uu____8693 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8745)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8753 = new_uvar r xs k_a in
                                    (match uu____8753 with
                                     | (gi_xs,gi) ->
                                         let gi_xs1 =
                                           FStar_TypeChecker_Normalize.eta_expand
                                             env1 gi_xs in
                                         let gi_ps =
                                           (FStar_Syntax_Syntax.mk_Tm_app gi
                                              ps)
                                             (Some
                                                (k_a.FStar_Syntax_Syntax.n))
                                             r in
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT
                                              (a, gi_xs1))
                                           :: subst1 in
                                         let uu____8772 = aux subst2 tl1 in
                                         (match uu____8772 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8787 =
                                                let uu____8789 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8789 :: gi_xs' in
                                              let uu____8790 =
                                                let uu____8792 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8792 :: gi_ps' in
                                              (uu____8787, uu____8790))) in
                              aux [] bs in
                        let uu____8795 =
                          let uu____8796 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8796 in
                        if uu____8795
                        then None
                        else
                          (let uu____8799 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8799 with
                           | (g_xs,uu____8806) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8813 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r in
                                 let uu____8818 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c) (fun _0_58  -> Some _0_58) in
                                 FStar_Syntax_Util.abs xs uu____8813
                                   uu____8818 in
                               let sub1 =
                                 let uu____8822 =
                                   let uu____8825 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let uu____8832 =
                                     let uu____8835 =
                                       FStar_List.map
                                         (fun uu____8841  ->
                                            match uu____8841 with
                                            | (uu____8846,uu____8847,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____8835 in
                                   mk_problem (p_scope orig) orig uu____8825
                                     (p_rel orig) uu____8832 None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____8822 in
                               ((let uu____8857 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____8857
                                 then
                                   let uu____8858 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____8859 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8858 uu____8859
                                 else ());
                                (let wl2 =
                                   let uu____8862 =
                                     let uu____8864 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives.fst (p_guard sub1) in
                                     Some uu____8864 in
                                   solve_prob orig uu____8862
                                     [TERM (u, proj)] wl1 in
                                 let uu____8869 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_60  -> Some _0_60) uu____8869))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8893 = lhs in
          match uu____8893 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8916 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____8916 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8942 =
                        let uu____8968 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____8968) in
                      Some uu____8942
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____9051 =
                           let uu____9055 =
                             let uu____9056 = FStar_Syntax_Subst.compress k in
                             uu____9056.FStar_Syntax_Syntax.n in
                           (uu____9055, args) in
                         match uu____9051 with
                         | (uu____9063,[]) ->
                             let uu____9065 =
                               let uu____9071 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____9071) in
                             Some uu____9065
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____9082,uu____9083) ->
                             let uu____9094 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9094 with
                              | (uv1,uv_args) ->
                                  let uu____9123 =
                                    let uu____9124 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9124.FStar_Syntax_Syntax.n in
                                  (match uu____9123 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9131) ->
                                       let uu____9144 =
                                         pat_vars env [] uv_args in
                                       (match uu____9144 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9158  ->
                                                      let uu____9159 =
                                                        let uu____9160 =
                                                          let uu____9161 =
                                                            let uu____9164 =
                                                              let uu____9165
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9165
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9164 in
                                                          fst uu____9161 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9160 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9159)) in
                                            let c1 =
                                              let uu____9171 =
                                                let uu____9172 =
                                                  let uu____9175 =
                                                    let uu____9176 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9176
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9175 in
                                                fst uu____9172 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9171 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9185 =
                                                let uu____9187 =
                                                  let uu____9188 =
                                                    let uu____9191 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9191
                                                      FStar_Pervasives.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____9188 in
                                                Some uu____9187 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9185 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9201 -> None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9204,uu____9205)
                             ->
                             let uu____9217 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9217 with
                              | (uv1,uv_args) ->
                                  let uu____9246 =
                                    let uu____9247 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9247.FStar_Syntax_Syntax.n in
                                  (match uu____9246 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9254) ->
                                       let uu____9267 =
                                         pat_vars env [] uv_args in
                                       (match uu____9267 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9281  ->
                                                      let uu____9282 =
                                                        let uu____9283 =
                                                          let uu____9284 =
                                                            let uu____9287 =
                                                              let uu____9288
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9288
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9287 in
                                                          fst uu____9284 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9283 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9282)) in
                                            let c1 =
                                              let uu____9294 =
                                                let uu____9295 =
                                                  let uu____9298 =
                                                    let uu____9299 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9299
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9298 in
                                                fst uu____9295 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9294 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9308 =
                                                let uu____9310 =
                                                  let uu____9311 =
                                                    let uu____9314 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9314
                                                      FStar_Pervasives.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____9311 in
                                                Some uu____9310 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9308 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9324 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9329)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____9361 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____9361
                                 (fun _0_61  -> Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9385 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____9385 with
                                  | (args1,rest) ->
                                      let uu____9403 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____9403 with
                                       | (xs2,c2) ->
                                           let uu____9411 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____9411
                                             (fun uu____9422  ->
                                                match uu____9422 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9444 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____9444 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____9492 =
                                        let uu____9495 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9495 in
                                      FStar_All.pipe_right uu____9492
                                        (fun _0_62  -> Some _0_62))
                         | uu____9503 ->
                             let uu____9507 =
                               let uu____9508 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____9509 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____9510 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9508 uu____9509 uu____9510 in
                             failwith uu____9507 in
                       let uu____9514 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____9514
                         (fun uu____9542  ->
                            match uu____9542 with
                            | (xs1,c1) ->
                                let uu____9570 =
                                  let uu____9593 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9593) in
                                Some uu____9570)) in
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
                     let uu____9665 = imitate orig env wl1 st in
                     match uu____9665 with
                     | Failed uu____9670 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9676 = project orig env wl1 i st in
                      match uu____9676 with
                      | None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some (Failed uu____9683) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____9697 = FStar_Syntax_Util.head_and_args t21 in
                match uu____9697 with
                | (hd1,uu____9708) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9723 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9731 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9732 -> true
                     | uu____9742 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____9745 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____9745
                         then true
                         else
                           ((let uu____9748 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____9748
                             then
                               let uu____9749 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9749
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9757 =
                    let uu____9760 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____9760 FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____9757 FStar_Syntax_Free.names in
                let uu____9791 = FStar_Util.set_is_empty fvs_hd in
                if uu____9791
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____9800 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____9800 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9808 =
                            let uu____9809 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____9809 in
                          giveup_or_defer1 orig uu____9808
                        else
                          (let uu____9811 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____9811
                           then
                             let uu____9812 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____9812
                              then
                                let uu____9813 = subterms args_lhs in
                                imitate' orig env wl1 uu____9813
                              else
                                ((let uu____9817 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____9817
                                  then
                                    let uu____9818 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____9819 = names_to_string fvs1 in
                                    let uu____9820 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9818 uu____9819 uu____9820
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9825 ->
                                        let uu____9826 = sn_binders env vars in
                                        u_abs k_uv uu____9826 t21 in
                                  let wl2 =
                                    solve_prob orig None
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
                               (let uu____9835 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____9835
                                then
                                  ((let uu____9837 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____9837
                                    then
                                      let uu____9838 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____9839 = names_to_string fvs1 in
                                      let uu____9840 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9838 uu____9839 uu____9840
                                    else ());
                                   (let uu____9842 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9842
                                      (- (Prims.parse_int "1"))))
                                else
                                  giveup env
                                    "free-variable check failed on a non-redex"
                                    orig)))
               | None  when patterns_only -> giveup env "not a pattern" orig
               | None  ->
                   if wl1.defer_ok
                   then solve env (defer "not a pattern" orig wl1)
                   else
                     (let uu____9856 =
                        let uu____9857 = FStar_Syntax_Free.names t1 in
                        check_head uu____9857 t2 in
                      if uu____9856
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____9861 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____9861
                          then
                            let uu____9862 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9862
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9865 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9865 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9910 =
               match uu____9910 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k in
                   let uu____9941 = FStar_Syntax_Util.arrow_formals k1 in
                   (match uu____9941 with
                    | (all_formals,uu____9952) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____10044  ->
                                        match uu____10044 with
                                        | (x,imp) ->
                                            let uu____10051 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____10051, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____10059 = FStar_Syntax_Util.type_u () in
                                match uu____10059 with
                                | (t1,uu____10063) ->
                                    let uu____10064 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    fst uu____10064 in
                              let uu____10067 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____10067 with
                               | (t',tm_u1) ->
                                   let uu____10074 = destruct_flex_t t' in
                                   (match uu____10074 with
                                    | (uu____10094,u1,k11,uu____10097) ->
                                        let sol =
                                          let uu____10125 =
                                            let uu____10130 =
                                              u_abs k1 all_formals t' in
                                            ((u, k1), uu____10130) in
                                          TERM uu____10125 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10190 = pat_var_opt env pat_args hd1 in
                              (match uu____10190 with
                               | None  ->
                                   aux pat_args pattern_vars pattern_var_set
                                     formals1 tl1
                               | Some y ->
                                   let maybe_pat =
                                     match xs_opt with
                                     | None  -> true
                                     | Some xs ->
                                         FStar_All.pipe_right xs
                                           (FStar_Util.for_some
                                              (fun uu____10219  ->
                                                 match uu____10219 with
                                                 | (x,uu____10223) ->
                                                     FStar_Syntax_Syntax.bv_eq
                                                       x (fst y))) in
                                   if Prims.op_Negation maybe_pat
                                   then
                                     aux pat_args pattern_vars
                                       pattern_var_set formals1 tl1
                                   else
                                     (let fvs =
                                        FStar_Syntax_Free.names
                                          (fst y).FStar_Syntax_Syntax.sort in
                                      let uu____10229 =
                                        let uu____10230 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____10230 in
                                      if uu____10229
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10234 =
                                           FStar_Util.set_add (fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10234 formals1
                                           tl1)))
                          | uu____10240 -> failwith "Impossible" in
                        let uu____10251 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____10251 all_formals args) in
             let solve_both_pats wl1 uu____10291 uu____10292 r =
               match (uu____10291, uu____10292) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10406 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____10406
                   then
                     let uu____10407 = solve_prob orig None [] wl1 in
                     solve env uu____10407
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____10422 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____10422
                       then
                         let uu____10423 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____10424 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____10425 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____10426 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____10427 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10423 uu____10424 uu____10425 uu____10426
                           uu____10427
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____10475 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____10475 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10488 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____10488 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10520 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10520 in
                                  let uu____10523 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____10523 k3)
                           else
                             (let uu____10526 =
                                let uu____10527 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____10528 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____10529 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10527 uu____10528 uu____10529 in
                              failwith uu____10526) in
                       let uu____10530 =
                         let uu____10536 =
                           let uu____10544 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____10544 in
                         match uu____10536 with
                         | (bs,k1') ->
                             let uu____10562 =
                               let uu____10570 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____10570 in
                             (match uu____10562 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____10591 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____10591 in
                                  let uu____10596 =
                                    let uu____10599 =
                                      let uu____10600 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____10600.FStar_Syntax_Syntax.n in
                                    let uu____10603 =
                                      let uu____10604 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____10604.FStar_Syntax_Syntax.n in
                                    (uu____10599, uu____10603) in
                                  (match uu____10596 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10612,uu____10613) ->
                                       (k1', [sub_prob])
                                   | (uu____10617,FStar_Syntax_Syntax.Tm_type
                                      uu____10618) -> (k2', [sub_prob])
                                   | uu____10622 ->
                                       let uu____10625 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____10625 with
                                        | (t,uu____10634) ->
                                            let uu____10635 = new_uvar r zs t in
                                            (match uu____10635 with
                                             | (k_zs,uu____10644) ->
                                                 let kprob =
                                                   let uu____10646 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_64  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_64) uu____10646 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____10530 with
                       | (k_u',sub_probs) ->
                           let uu____10660 =
                             let uu____10668 =
                               let uu____10669 = new_uvar r zs k_u' in
                               FStar_All.pipe_left FStar_Pervasives.fst
                                 uu____10669 in
                             let uu____10674 =
                               let uu____10677 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____10677 in
                             let uu____10680 =
                               let uu____10683 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____10683 in
                             (uu____10668, uu____10674, uu____10680) in
                           (match uu____10660 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____10702 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____10702 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____10714 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____10714
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____10718 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____10718 with
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
                                                    solve_prob orig None
                                                      [sol1; sol2] wl1 in
                                                  solve env
                                                    (attempt sub_probs wl2)))))))) in
             let solve_one_pat uu____10750 uu____10751 =
               match (uu____10750, uu____10751) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10815 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____10815
                     then
                       let uu____10816 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10817 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10816 uu____10817
                     else ());
                    (let uu____10819 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____10819
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10826  ->
                              fun uu____10827  ->
                                match (uu____10826, uu____10827) with
                                | ((a,uu____10837),(t21,uu____10839)) ->
                                    let uu____10844 =
                                      let uu____10847 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____10847
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____10844
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2 in
                       let guard =
                         let uu____10851 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____10851 in
                       let wl1 = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____10861 = occurs_check env wl (u1, k1) t21 in
                        match uu____10861 with
                        | (occurs_ok,uu____10866) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____10871 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____10871
                            then
                              let sol =
                                let uu____10873 =
                                  let uu____10878 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____10878) in
                                TERM uu____10873 in
                              let wl1 = solve_prob orig None [sol] wl in
                              solve env wl1
                            else
                              (let uu____10883 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____10883
                               then
                                 let uu____10884 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____10884 with
                                 | (sol,(uu____10894,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____10904 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____10904
                                       then
                                         let uu____10905 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10905
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10910 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____10912 = lhs in
             match uu____10912 with
             | (t1,u1,k1,args1) ->
                 let uu____10917 = rhs in
                 (match uu____10917 with
                  | (t2,u2,k2,args2) ->
                      let maybe_pat_vars1 = pat_vars env [] args1 in
                      let maybe_pat_vars2 = pat_vars env [] args2 in
                      let r = t2.FStar_Syntax_Syntax.pos in
                      (match (maybe_pat_vars1, maybe_pat_vars2) with
                       | (Some xs,Some ys) ->
                           solve_both_pats wl (u1, k1, xs, args1)
                             (u2, k2, ys, args2) t2.FStar_Syntax_Syntax.pos
                       | (Some xs,None ) ->
                           solve_one_pat (t1, u1, k1, xs) rhs
                       | (None ,Some ys) ->
                           solve_one_pat (t2, u2, k2, ys) lhs
                       | uu____10943 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____10949 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____10949 with
                              | (sol,uu____10956) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____10959 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____10959
                                    then
                                      let uu____10960 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____10960
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____10965 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____10967 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____10967
        then
          let uu____10968 = solve_prob orig None [] wl in
          solve env uu____10968
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____10972 = FStar_Util.physical_equality t1 t2 in
           if uu____10972
           then
             let uu____10973 = solve_prob orig None [] wl in
             solve env uu____10973
           else
             ((let uu____10976 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____10976
               then
                 let uu____10977 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____10977
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____10980,uu____10981) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____10982,FStar_Syntax_Syntax.Tm_bvar uu____10983) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___132_11023 =
                     match uu___132_11023 with
                     | [] -> c
                     | bs ->
                         let uu____11037 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c)) None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____11037 in
                   let uu____11047 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____11047 with
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
                                   let uu____11133 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____11133
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____11135 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____11135))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___133_11187 =
                     match uu___133_11187 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l)) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____11212 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____11212 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11295 =
                                   let uu____11298 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____11299 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____11298
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11299 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____11295))
               | (FStar_Syntax_Syntax.Tm_abs uu____11302,uu____11303) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11321 -> true
                     | uu____11331 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11359 =
                     let uu____11370 = maybe_eta t1 in
                     let uu____11375 = maybe_eta t2 in
                     (uu____11370, uu____11375) in
                   (match uu____11359 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_11406 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_11406.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_11406.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_11406.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_11406.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_11406.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_11406.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_11406.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_11406.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11425 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11425
                        then
                          let uu____11426 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11426 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11447 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11447
                        then
                          let uu____11448 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11448 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11453 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11464,FStar_Syntax_Syntax.Tm_abs uu____11465) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11483 -> true
                     | uu____11493 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11521 =
                     let uu____11532 = maybe_eta t1 in
                     let uu____11537 = maybe_eta t2 in
                     (uu____11532, uu____11537) in
                   (match uu____11521 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_11568 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_11568.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_11568.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_11568.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_11568.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_11568.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_11568.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_11568.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_11568.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11587 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11587
                        then
                          let uu____11588 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11588 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11609 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11609
                        then
                          let uu____11610 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11610 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11615 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11626,FStar_Syntax_Syntax.Tm_refine uu____11627) ->
                   let uu____11636 = as_refinement env wl t1 in
                   (match uu____11636 with
                    | (x1,phi1) ->
                        let uu____11641 = as_refinement env wl t2 in
                        (match uu____11641 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11647 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____11647 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____11680 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____11680
                                 (guard_on_element wl problem x11) in
                             let fallback uu____11684 =
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
                                 let uu____11690 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____11690 impl in
                               let wl1 = solve_prob orig (Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11697 =
                                   let uu____11700 =
                                     let uu____11701 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____11701 :: (p_scope orig) in
                                   mk_problem uu____11700 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____11697 in
                               let uu____11704 =
                                 solve env1
                                   (let uu___167_11705 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___167_11705.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___167_11705.smt_ok);
                                      tcenv = (uu___167_11705.tcenv)
                                    }) in
                               (match uu____11704 with
                                | Failed uu____11709 -> fallback ()
                                | Success uu____11712 ->
                                    let guard =
                                      let uu____11716 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives.fst in
                                      let uu____11719 =
                                        let uu____11720 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives.fst in
                                        FStar_All.pipe_right uu____11720
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____11716
                                        uu____11719 in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl2 =
                                      let uu___168_11727 = wl1 in
                                      {
                                        attempting =
                                          (uu___168_11727.attempting);
                                        wl_deferred =
                                          (uu___168_11727.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___168_11727.defer_ok);
                                        smt_ok = (uu___168_11727.smt_ok);
                                        tcenv = (uu___168_11727.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11729,FStar_Syntax_Syntax.Tm_uvar uu____11730) ->
                   let uu____11747 = destruct_flex_t t1 in
                   let uu____11748 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11747 uu____11748
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11749;
                     FStar_Syntax_Syntax.tk = uu____11750;
                     FStar_Syntax_Syntax.pos = uu____11751;
                     FStar_Syntax_Syntax.vars = uu____11752;_},uu____11753),FStar_Syntax_Syntax.Tm_uvar
                  uu____11754) ->
                   let uu____11785 = destruct_flex_t t1 in
                   let uu____11786 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11785 uu____11786
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11787,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11788;
                     FStar_Syntax_Syntax.tk = uu____11789;
                     FStar_Syntax_Syntax.pos = uu____11790;
                     FStar_Syntax_Syntax.vars = uu____11791;_},uu____11792))
                   ->
                   let uu____11823 = destruct_flex_t t1 in
                   let uu____11824 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11823 uu____11824
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11825;
                     FStar_Syntax_Syntax.tk = uu____11826;
                     FStar_Syntax_Syntax.pos = uu____11827;
                     FStar_Syntax_Syntax.vars = uu____11828;_},uu____11829),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11830;
                     FStar_Syntax_Syntax.tk = uu____11831;
                     FStar_Syntax_Syntax.pos = uu____11832;
                     FStar_Syntax_Syntax.vars = uu____11833;_},uu____11834))
                   ->
                   let uu____11879 = destruct_flex_t t1 in
                   let uu____11880 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11879 uu____11880
               | (FStar_Syntax_Syntax.Tm_uvar uu____11881,uu____11882) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11891 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11891 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11895;
                     FStar_Syntax_Syntax.tk = uu____11896;
                     FStar_Syntax_Syntax.pos = uu____11897;
                     FStar_Syntax_Syntax.vars = uu____11898;_},uu____11899),uu____11900)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11923 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11923 t2 wl
               | (uu____11927,FStar_Syntax_Syntax.Tm_uvar uu____11928) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____11937,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11938;
                     FStar_Syntax_Syntax.tk = uu____11939;
                     FStar_Syntax_Syntax.pos = uu____11940;
                     FStar_Syntax_Syntax.vars = uu____11941;_},uu____11942))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11965,FStar_Syntax_Syntax.Tm_type uu____11966) ->
                   solve_t' env
                     (let uu___169_11975 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_11975.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_11975.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_11975.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_11975.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_11975.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_11975.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_11975.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_11975.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_11975.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11976;
                     FStar_Syntax_Syntax.tk = uu____11977;
                     FStar_Syntax_Syntax.pos = uu____11978;
                     FStar_Syntax_Syntax.vars = uu____11979;_},uu____11980),FStar_Syntax_Syntax.Tm_type
                  uu____11981) ->
                   solve_t' env
                     (let uu___169_12004 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12004.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12004.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12004.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12004.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12004.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12004.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12004.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12004.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12004.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12005,FStar_Syntax_Syntax.Tm_arrow uu____12006) ->
                   solve_t' env
                     (let uu___169_12022 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12022.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12022.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12022.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12022.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12022.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12022.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12022.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12022.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12022.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12023;
                     FStar_Syntax_Syntax.tk = uu____12024;
                     FStar_Syntax_Syntax.pos = uu____12025;
                     FStar_Syntax_Syntax.vars = uu____12026;_},uu____12027),FStar_Syntax_Syntax.Tm_arrow
                  uu____12028) ->
                   solve_t' env
                     (let uu___169_12058 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12058.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12058.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12058.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12058.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12058.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12058.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12058.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12058.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12058.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____12059,uu____12060) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12071 =
                        let uu____12072 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12072 in
                      if uu____12071
                      then
                        let uu____12073 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___170_12076 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_12076.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_12076.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_12076.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_12076.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_12076.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_12076.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_12076.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_12076.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_12076.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12077 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12073 uu____12077 t2
                          wl
                      else
                        (let uu____12082 = base_and_refinement env wl t2 in
                         match uu____12082 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12112 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___171_12115 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_12115.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_12115.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_12115.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_12115.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_12115.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_12115.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_12115.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_12115.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_12115.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12116 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12112
                                    uu____12116 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___172_12131 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_12131.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_12131.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12134 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____12134 in
                                  let guard =
                                    let uu____12142 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12142
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12148;
                     FStar_Syntax_Syntax.tk = uu____12149;
                     FStar_Syntax_Syntax.pos = uu____12150;
                     FStar_Syntax_Syntax.vars = uu____12151;_},uu____12152),uu____12153)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12178 =
                        let uu____12179 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12179 in
                      if uu____12178
                      then
                        let uu____12180 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___170_12183 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_12183.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_12183.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_12183.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_12183.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_12183.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_12183.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_12183.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_12183.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_12183.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12184 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12180 uu____12184 t2
                          wl
                      else
                        (let uu____12189 = base_and_refinement env wl t2 in
                         match uu____12189 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12219 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___171_12222 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_12222.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_12222.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_12222.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_12222.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_12222.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_12222.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_12222.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_12222.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_12222.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12223 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12219
                                    uu____12223 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___172_12238 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_12238.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_12238.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12241 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____12241 in
                                  let guard =
                                    let uu____12249 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12249
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12255,FStar_Syntax_Syntax.Tm_uvar uu____12256) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12266 = base_and_refinement env wl t1 in
                      match uu____12266 with
                      | (t_base,uu____12277) ->
                          solve_t env
                            (let uu___173_12292 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_12292.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_12292.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_12292.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_12292.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_12292.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_12292.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_12292.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_12292.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12295,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12296;
                     FStar_Syntax_Syntax.tk = uu____12297;
                     FStar_Syntax_Syntax.pos = uu____12298;
                     FStar_Syntax_Syntax.vars = uu____12299;_},uu____12300))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12324 = base_and_refinement env wl t1 in
                      match uu____12324 with
                      | (t_base,uu____12335) ->
                          solve_t env
                            (let uu___173_12350 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_12350.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_12350.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_12350.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_12350.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_12350.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_12350.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_12350.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_12350.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12353,uu____12354) ->
                   let t21 =
                     let uu____12362 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____12362 in
                   solve_t env
                     (let uu___174_12375 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_12375.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___174_12375.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___174_12375.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___174_12375.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_12375.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_12375.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_12375.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_12375.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_12375.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12376,FStar_Syntax_Syntax.Tm_refine uu____12377) ->
                   let t11 =
                     let uu____12385 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____12385 in
                   solve_t env
                     (let uu___175_12398 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_12398.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_12398.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_12398.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_12398.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_12398.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_12398.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_12398.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_12398.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_12398.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12401,uu____12402) ->
                   let head1 =
                     let uu____12421 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12421 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12452 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12452 FStar_Pervasives.fst in
                   let uu____12480 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12480
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12489 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12489
                      then
                        let guard =
                          let uu____12496 =
                            let uu____12497 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12497 = FStar_Syntax_Util.Equal in
                          if uu____12496
                          then None
                          else
                            (let uu____12500 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_76  -> Some _0_76)
                               uu____12500) in
                        let uu____12502 = solve_prob orig guard [] wl in
                        solve env uu____12502
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12505,uu____12506) ->
                   let head1 =
                     let uu____12514 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12514 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12545 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12545 FStar_Pervasives.fst in
                   let uu____12573 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12573
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12582 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12582
                      then
                        let guard =
                          let uu____12589 =
                            let uu____12590 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12590 = FStar_Syntax_Util.Equal in
                          if uu____12589
                          then None
                          else
                            (let uu____12593 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_77  -> Some _0_77)
                               uu____12593) in
                        let uu____12595 = solve_prob orig guard [] wl in
                        solve env uu____12595
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12598,uu____12599) ->
                   let head1 =
                     let uu____12603 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12603 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12634 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12634 FStar_Pervasives.fst in
                   let uu____12662 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12662
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12671 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12671
                      then
                        let guard =
                          let uu____12678 =
                            let uu____12679 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12679 = FStar_Syntax_Util.Equal in
                          if uu____12678
                          then None
                          else
                            (let uu____12682 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_78  -> Some _0_78)
                               uu____12682) in
                        let uu____12684 = solve_prob orig guard [] wl in
                        solve env uu____12684
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12687,uu____12688) ->
                   let head1 =
                     let uu____12692 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12692 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12723 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12723 FStar_Pervasives.fst in
                   let uu____12751 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12751
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12760 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12760
                      then
                        let guard =
                          let uu____12767 =
                            let uu____12768 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12768 = FStar_Syntax_Util.Equal in
                          if uu____12767
                          then None
                          else
                            (let uu____12771 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_79  -> Some _0_79)
                               uu____12771) in
                        let uu____12773 = solve_prob orig guard [] wl in
                        solve env uu____12773
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____12776,uu____12777) ->
                   let head1 =
                     let uu____12781 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12781 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12812 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12812 FStar_Pervasives.fst in
                   let uu____12840 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12840
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12849 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12849
                      then
                        let guard =
                          let uu____12856 =
                            let uu____12857 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12857 = FStar_Syntax_Util.Equal in
                          if uu____12856
                          then None
                          else
                            (let uu____12860 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_80  -> Some _0_80)
                               uu____12860) in
                        let uu____12862 = solve_prob orig guard [] wl in
                        solve env uu____12862
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____12865,uu____12866) ->
                   let head1 =
                     let uu____12879 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12879 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12910 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12910 FStar_Pervasives.fst in
                   let uu____12938 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12938
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12947 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12947
                      then
                        let guard =
                          let uu____12954 =
                            let uu____12955 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12955 = FStar_Syntax_Util.Equal in
                          if uu____12954
                          then None
                          else
                            (let uu____12958 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_81  -> Some _0_81)
                               uu____12958) in
                        let uu____12960 = solve_prob orig guard [] wl in
                        solve env uu____12960
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12963,FStar_Syntax_Syntax.Tm_match uu____12964) ->
                   let head1 =
                     let uu____12983 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12983 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13014 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13014 FStar_Pervasives.fst in
                   let uu____13042 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13042
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13051 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13051
                      then
                        let guard =
                          let uu____13058 =
                            let uu____13059 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13059 = FStar_Syntax_Util.Equal in
                          if uu____13058
                          then None
                          else
                            (let uu____13062 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_82  -> Some _0_82)
                               uu____13062) in
                        let uu____13064 = solve_prob orig guard [] wl in
                        solve env uu____13064
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13067,FStar_Syntax_Syntax.Tm_uinst uu____13068) ->
                   let head1 =
                     let uu____13076 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13076 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13107 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13107 FStar_Pervasives.fst in
                   let uu____13135 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13135
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13144 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13144
                      then
                        let guard =
                          let uu____13151 =
                            let uu____13152 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13152 = FStar_Syntax_Util.Equal in
                          if uu____13151
                          then None
                          else
                            (let uu____13155 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_83  -> Some _0_83)
                               uu____13155) in
                        let uu____13157 = solve_prob orig guard [] wl in
                        solve env uu____13157
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13160,FStar_Syntax_Syntax.Tm_name uu____13161) ->
                   let head1 =
                     let uu____13165 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13165 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13196 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13196 FStar_Pervasives.fst in
                   let uu____13224 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13224
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13233 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13233
                      then
                        let guard =
                          let uu____13240 =
                            let uu____13241 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13241 = FStar_Syntax_Util.Equal in
                          if uu____13240
                          then None
                          else
                            (let uu____13244 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_84  -> Some _0_84)
                               uu____13244) in
                        let uu____13246 = solve_prob orig guard [] wl in
                        solve env uu____13246
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13249,FStar_Syntax_Syntax.Tm_constant uu____13250) ->
                   let head1 =
                     let uu____13254 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13254 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13285 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13285 FStar_Pervasives.fst in
                   let uu____13313 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13313
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13322 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13322
                      then
                        let guard =
                          let uu____13329 =
                            let uu____13330 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13330 = FStar_Syntax_Util.Equal in
                          if uu____13329
                          then None
                          else
                            (let uu____13333 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_85  -> Some _0_85)
                               uu____13333) in
                        let uu____13335 = solve_prob orig guard [] wl in
                        solve env uu____13335
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13338,FStar_Syntax_Syntax.Tm_fvar uu____13339) ->
                   let head1 =
                     let uu____13343 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13343 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13374 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13374 FStar_Pervasives.fst in
                   let uu____13402 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13402
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13411 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13411
                      then
                        let guard =
                          let uu____13418 =
                            let uu____13419 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13419 = FStar_Syntax_Util.Equal in
                          if uu____13418
                          then None
                          else
                            (let uu____13422 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_86  -> Some _0_86)
                               uu____13422) in
                        let uu____13424 = solve_prob orig guard [] wl in
                        solve env uu____13424
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13427,FStar_Syntax_Syntax.Tm_app uu____13428) ->
                   let head1 =
                     let uu____13441 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13441 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13472 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13472 FStar_Pervasives.fst in
                   let uu____13500 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13500
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13509 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13509
                      then
                        let guard =
                          let uu____13516 =
                            let uu____13517 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13517 = FStar_Syntax_Util.Equal in
                          if uu____13516
                          then None
                          else
                            (let uu____13520 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_87  -> Some _0_87)
                               uu____13520) in
                        let uu____13522 = solve_prob orig guard [] wl in
                        solve env uu____13522
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13526,uu____13527),uu____13528) ->
                   solve_t' env
                     (let uu___176_13557 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_13557.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___176_13557.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___176_13557.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___176_13557.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_13557.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_13557.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_13557.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_13557.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_13557.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13560,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13562,uu____13563)) ->
                   solve_t' env
                     (let uu___177_13592 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___177_13592.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___177_13592.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___177_13592.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___177_13592.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___177_13592.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___177_13592.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___177_13592.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___177_13592.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___177_13592.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13593,uu____13594) ->
                   let uu____13602 =
                     let uu____13603 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13604 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13603
                       uu____13604 in
                   failwith uu____13602
               | (FStar_Syntax_Syntax.Tm_meta uu____13605,uu____13606) ->
                   let uu____13611 =
                     let uu____13612 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13613 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13612
                       uu____13613 in
                   failwith uu____13611
               | (FStar_Syntax_Syntax.Tm_delayed uu____13614,uu____13615) ->
                   let uu____13630 =
                     let uu____13631 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13632 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13631
                       uu____13632 in
                   failwith uu____13630
               | (uu____13633,FStar_Syntax_Syntax.Tm_meta uu____13634) ->
                   let uu____13639 =
                     let uu____13640 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13641 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13640
                       uu____13641 in
                   failwith uu____13639
               | (uu____13642,FStar_Syntax_Syntax.Tm_delayed uu____13643) ->
                   let uu____13658 =
                     let uu____13659 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13660 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13659
                       uu____13660 in
                   failwith uu____13658
               | (uu____13661,FStar_Syntax_Syntax.Tm_let uu____13662) ->
                   let uu____13670 =
                     let uu____13671 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13672 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13671
                       uu____13672 in
                   failwith uu____13670
               | uu____13673 -> giveup env "head tag mismatch" orig)))
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
          mk_problem (p_scope orig) orig t1 rel t2 None reason in
        let solve_eq c1_comp c2_comp =
          (let uu____13705 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____13705
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____13713  ->
                  fun uu____13714  ->
                    match (uu____13713, uu____13714) with
                    | ((a1,uu____13724),(a2,uu____13726)) ->
                        let uu____13731 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_88  -> FStar_TypeChecker_Common.TProb _0_88)
                          uu____13731)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____13737 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p) FStar_Pervasives.fst)
                 sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____13737 in
           let wl1 = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____13757 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____13764)::[] -> wp1
              | uu____13777 ->
                  let uu____13783 =
                    let uu____13784 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____13784 in
                  failwith uu____13783 in
            let uu____13787 =
              let uu____13793 =
                let uu____13794 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____13794 in
              [uu____13793] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____13787;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____13795 = lift_c1 () in solve_eq uu____13795 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___134_13799  ->
                       match uu___134_13799 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____13800 -> false)) in
             let uu____13801 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____13825)::uu____13826,(wp2,uu____13828)::uu____13829)
                   -> (wp1, wp2)
               | uu____13870 ->
                   let uu____13883 =
                     let uu____13884 =
                       let uu____13887 =
                         let uu____13888 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____13889 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____13888 uu____13889 in
                       (uu____13887, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____13884 in
                   raise uu____13883 in
             match uu____13801 with
             | (wpc1,wpc2) ->
                 let uu____13906 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____13906
                 then
                   let uu____13909 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env uu____13909 wl
                 else
                   (let uu____13913 =
                      let uu____13917 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____13917 in
                    match uu____13913 with
                    | (c2_decl,qualifiers) ->
                        let uu____13929 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____13929
                        then
                          let c1_repr =
                            let uu____13932 =
                              let uu____13933 =
                                let uu____13934 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____13934 in
                              let uu____13935 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13933 uu____13935 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13932 in
                          let c2_repr =
                            let uu____13937 =
                              let uu____13938 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____13939 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13938 uu____13939 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13937 in
                          let prob =
                            let uu____13941 =
                              let uu____13944 =
                                let uu____13945 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____13946 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____13945
                                  uu____13946 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____13944 in
                            FStar_TypeChecker_Common.TProb uu____13941 in
                          let wl1 =
                            let uu____13948 =
                              let uu____13950 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives.fst in
                              Some uu____13950 in
                            solve_prob orig uu____13948 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____13957 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____13957
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____13959 =
                                     let uu____13962 =
                                       let uu____13963 =
                                         let uu____13973 =
                                           let uu____13974 =
                                             let uu____13975 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____13975] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____13974 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____13976 =
                                           let uu____13978 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____13979 =
                                             let uu____13981 =
                                               let uu____13982 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____13982 in
                                             [uu____13981] in
                                           uu____13978 :: uu____13979 in
                                         (uu____13973, uu____13976) in
                                       FStar_Syntax_Syntax.Tm_app uu____13963 in
                                     FStar_Syntax_Syntax.mk uu____13962 in
                                   uu____13959
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____13993 =
                                    let uu____13996 =
                                      let uu____13997 =
                                        let uu____14007 =
                                          let uu____14008 =
                                            let uu____14009 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____14009] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____14008 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____14010 =
                                          let uu____14012 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____14013 =
                                            let uu____14015 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____14016 =
                                              let uu____14018 =
                                                let uu____14019 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14019 in
                                              [uu____14018] in
                                            uu____14015 :: uu____14016 in
                                          uu____14012 :: uu____14013 in
                                        (uu____14007, uu____14010) in
                                      FStar_Syntax_Syntax.Tm_app uu____13997 in
                                    FStar_Syntax_Syntax.mk uu____13996 in
                                  uu____13993
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____14030 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____14030 in
                           let wl1 =
                             let uu____14036 =
                               let uu____14038 =
                                 let uu____14041 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____14041 g in
                               FStar_All.pipe_left (fun _0_90  -> Some _0_90)
                                 uu____14038 in
                             solve_prob orig uu____14036 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____14051 = FStar_Util.physical_equality c1 c2 in
        if uu____14051
        then
          let uu____14052 = solve_prob orig None [] wl in
          solve env uu____14052
        else
          ((let uu____14055 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____14055
            then
              let uu____14056 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____14057 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14056
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14057
            else ());
           (let uu____14059 =
              let uu____14062 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____14063 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____14062, uu____14063) in
            match uu____14059 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14067),FStar_Syntax_Syntax.Total
                    (t2,uu____14069)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14082 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14082 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14085,FStar_Syntax_Syntax.Total uu____14086) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14098),FStar_Syntax_Syntax.Total
                    (t2,uu____14100)) ->
                     let uu____14113 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14113 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14117),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14119)) ->
                     let uu____14132 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14132 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14136),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14138)) ->
                     let uu____14151 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14151 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14154,FStar_Syntax_Syntax.Comp uu____14155) ->
                     let uu____14161 =
                       let uu___178_14164 = problem in
                       let uu____14167 =
                         let uu____14168 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14168 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14164.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14167;
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14164.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___178_14164.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___178_14164.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14164.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14164.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14164.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14164.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14164.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14161 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14169,FStar_Syntax_Syntax.Comp uu____14170) ->
                     let uu____14176 =
                       let uu___178_14179 = problem in
                       let uu____14182 =
                         let uu____14183 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14183 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14179.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14182;
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14179.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___178_14179.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___178_14179.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14179.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14179.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14179.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14179.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14179.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14176 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14184,FStar_Syntax_Syntax.GTotal uu____14185) ->
                     let uu____14191 =
                       let uu___179_14194 = problem in
                       let uu____14197 =
                         let uu____14198 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14198 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_14194.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___179_14194.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___179_14194.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14197;
                         FStar_TypeChecker_Common.element =
                           (uu___179_14194.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_14194.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_14194.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_14194.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_14194.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_14194.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14191 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14199,FStar_Syntax_Syntax.Total uu____14200) ->
                     let uu____14206 =
                       let uu___179_14209 = problem in
                       let uu____14212 =
                         let uu____14213 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14213 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_14209.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___179_14209.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___179_14209.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14212;
                         FStar_TypeChecker_Common.element =
                           (uu___179_14209.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_14209.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_14209.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_14209.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_14209.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_14209.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14206 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14214,FStar_Syntax_Syntax.Comp uu____14215) ->
                     let uu____14216 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____14216
                     then
                       let uu____14217 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type" in
                       solve_t env uu____14217 wl
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
                           (let uu____14227 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____14227
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14229 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____14229 with
                            | None  ->
                                let uu____14231 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14232 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____14232) in
                                if uu____14231
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
                                  (let uu____14235 =
                                     let uu____14236 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____14237 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14236 uu____14237 in
                                   giveup env uu____14235 orig)
                            | Some edge -> solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14243 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14259  ->
              match uu____14259 with
              | (uu____14266,uu____14267,u,uu____14269,uu____14270,uu____14271)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____14243 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14290 =
        FStar_All.pipe_right (fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____14290 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____14300 =
        FStar_All.pipe_right (snd ineqs)
          (FStar_List.map
             (fun uu____14312  ->
                match uu____14312 with
                | (u1,u2) ->
                    let uu____14317 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____14318 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____14317 uu____14318)) in
      FStar_All.pipe_right uu____14300 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14332,[])) -> "{}"
      | uu____14345 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14355 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____14355
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____14358 =
              FStar_List.map
                (fun uu____14362  ->
                   match uu____14362 with
                   | (uu____14365,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____14358 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____14369 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14369 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14414 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____14414
    then
      let uu____14415 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____14416 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14415
        (rel_to_string rel) uu____14416
    else "TOP" in
  let p = new_problem env lhs rel rhs elt loc reason in p
let new_t_prob:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.term ->
          (FStar_TypeChecker_Common.prob* FStar_Syntax_Syntax.bv)
  =
  fun env  ->
    fun t1  ->
      fun rel  ->
        fun t2  ->
          let x =
            let uu____14440 =
              let uu____14442 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_91  -> Some _0_91) uu____14442 in
            FStar_Syntax_Syntax.new_bv uu____14440 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____14448 =
              let uu____14450 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_92  -> Some _0_92) uu____14450 in
            let uu____14452 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____14448 uu____14452 in
          ((FStar_TypeChecker_Common.TProb p), x)
let solve_and_commit:
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob* Prims.string) ->
         FStar_TypeChecker_Common.deferred option)
        -> FStar_TypeChecker_Common.deferred option
  =
  fun env  ->
    fun probs  ->
      fun err1  ->
        let probs1 =
          let uu____14478 = FStar_Options.eager_inference () in
          if uu____14478
          then
            let uu___180_14479 = probs in
            {
              attempting = (uu___180_14479.attempting);
              wl_deferred = (uu___180_14479.wl_deferred);
              ctr = (uu___180_14479.ctr);
              defer_ok = false;
              smt_ok = (uu___180_14479.smt_ok);
              tcenv = (uu___180_14479.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Syntax_Unionfind.rollback tx;
             (let uu____14490 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____14490
              then
                let uu____14491 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____14491
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
          ((let uu____14503 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____14503
            then
              let uu____14504 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14504
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____14508 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____14508
             then
               let uu____14509 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14509
             else ());
            (let f2 =
               let uu____14512 =
                 let uu____14513 = FStar_Syntax_Util.unmeta f1 in
                 uu____14513.FStar_Syntax_Syntax.n in
               match uu____14512 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14517 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___181_14518 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___181_14518.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_14518.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_14518.FStar_TypeChecker_Env.implicits)
             })))
let with_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_TypeChecker_Common.deferred option ->
        FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | None  -> None
        | Some d ->
            let uu____14536 =
              let uu____14537 =
                let uu____14538 =
                  let uu____14539 =
                    FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____14539
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14538;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____14537 in
            FStar_All.pipe_left (fun _0_94  -> Some _0_94) uu____14536
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____14576 =
        let uu____14577 =
          let uu____14578 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
          FStar_All.pipe_right uu____14578
            (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
        {
          FStar_TypeChecker_Env.guard_f = uu____14577;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      Some uu____14576
let try_teq:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t option
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____14608 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14608
           then
             let uu____14609 = FStar_Syntax_Print.term_to_string t1 in
             let uu____14610 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14609
               uu____14610
           else ());
          (let prob =
             let uu____14613 =
               let uu____14616 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____14616 in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____14613 in
           let g =
             let uu____14621 =
               let uu____14623 = singleton' env prob smt_ok in
               solve_and_commit env uu____14623 (fun uu____14624  -> None) in
             FStar_All.pipe_left (with_guard env prob) uu____14621 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14641 = try_teq true env t1 t2 in
        match uu____14641 with
        | None  ->
            let uu____14643 =
              let uu____14644 =
                let uu____14647 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                let uu____14648 = FStar_TypeChecker_Env.get_range env in
                (uu____14647, uu____14648) in
              FStar_Errors.Error uu____14644 in
            raise uu____14643
        | Some g ->
            ((let uu____14651 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____14651
              then
                let uu____14652 = FStar_Syntax_Print.term_to_string t1 in
                let uu____14653 = FStar_Syntax_Print.term_to_string t2 in
                let uu____14654 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14652
                  uu____14653 uu____14654
              else ());
             g)
let try_subtype':
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        Prims.bool -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun smt_ok  ->
          (let uu____14674 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14674
           then
             let uu____14675 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____14676 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14675
               uu____14676
           else ());
          (let uu____14678 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____14678 with
           | (prob,x) ->
               let g =
                 let uu____14686 =
                   let uu____14688 = singleton' env prob smt_ok in
                   solve_and_commit env uu____14688
                     (fun uu____14689  -> None) in
                 FStar_All.pipe_left (with_guard env prob) uu____14686 in
               ((let uu____14695 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____14695
                 then
                   let uu____14696 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____14697 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____14698 =
                     let uu____14699 = FStar_Util.must g in
                     guard_to_string env uu____14699 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14696 uu____14697 uu____14698
                 else ());
                abstract_guard x g))
let try_subtype:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t option
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
          let uu____14730 = FStar_TypeChecker_Env.get_range env in
          let uu____14731 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.err uu____14730 uu____14731
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____14746 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____14746
         then
           let uu____14747 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____14748 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____14747
             uu____14748
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____14753 =
             let uu____14756 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None uu____14756 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____14753 in
         let uu____14759 =
           let uu____14761 = singleton env prob in
           solve_and_commit env uu____14761 (fun uu____14762  -> None) in
         FStar_All.pipe_left (with_guard env prob) uu____14759)
let solve_universe_inequalities':
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____14784  ->
        match uu____14784 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____14809 =
                 let uu____14810 =
                   let uu____14813 =
                     let uu____14814 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____14815 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____14814 uu____14815 in
                   let uu____14816 = FStar_TypeChecker_Env.get_range env in
                   (uu____14813, uu____14816) in
                 FStar_Errors.Error uu____14810 in
               raise uu____14809) in
            let equiv1 v1 v' =
              let uu____14824 =
                let uu____14827 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____14828 = FStar_Syntax_Subst.compress_univ v' in
                (uu____14827, uu____14828) in
              match uu____14824 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____14835 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____14849 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____14849 with
                      | FStar_Syntax_Syntax.U_unif uu____14853 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____14864  ->
                                    match uu____14864 with
                                    | (u,v') ->
                                        let uu____14870 = equiv1 v1 v' in
                                        if uu____14870
                                        then
                                          let uu____14872 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____14872 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____14882 -> [])) in
            let uu____14885 =
              let wl =
                let uu___182_14888 = empty_worklist env in
                {
                  attempting = (uu___182_14888.attempting);
                  wl_deferred = (uu___182_14888.wl_deferred);
                  ctr = (uu___182_14888.ctr);
                  defer_ok = false;
                  smt_ok = (uu___182_14888.smt_ok);
                  tcenv = (uu___182_14888.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____14895  ->
                      match uu____14895 with
                      | (lb,v1) ->
                          let uu____14900 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____14900 with
                           | USolved wl1 -> ()
                           | uu____14902 -> fail lb v1))) in
            let rec check_ineq uu____14908 =
              match uu____14908 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____14915) -> true
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
                      uu____14926,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____14928,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____14933) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____14937,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____14942 -> false) in
            let uu____14945 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____14951  ->
                      match uu____14951 with
                      | (u,v1) ->
                          let uu____14956 = check_ineq (u, v1) in
                          if uu____14956
                          then true
                          else
                            ((let uu____14959 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____14959
                              then
                                let uu____14960 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____14961 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____14960
                                  uu____14961
                              else ());
                             false))) in
            if uu____14945
            then ()
            else
              ((let uu____14965 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____14965
                then
                  ((let uu____14967 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____14967);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____14973 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____14973))
                else ());
               (let uu____14979 =
                  let uu____14980 =
                    let uu____14983 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____14983) in
                  FStar_Errors.Error uu____14980 in
                raise uu____14979))
let solve_universe_inequalities:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
      FStar_Syntax_Syntax.universe) Prims.list) -> Prims.unit
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
      let fail uu____15020 =
        match uu____15020 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____15030 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____15030
       then
         let uu____15031 = wl_to_string wl in
         let uu____15032 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____15031 uu____15032
       else ());
      (let g1 =
         let uu____15047 = solve_and_commit env wl fail in
         match uu____15047 with
         | Some [] ->
             let uu___183_15054 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___183_15054.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___183_15054.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___183_15054.FStar_TypeChecker_Env.implicits)
             }
         | uu____15057 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___184_15060 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___184_15060.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___184_15060.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___184_15060.FStar_TypeChecker_Env.implicits)
        }))
let discharge_guard':
  (Prims.unit -> Prims.string) option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool -> FStar_TypeChecker_Env.guard_t option
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let g1 = solve_deferred_constraints env g in
          let ret_g =
            let uu___185_15090 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___185_15090.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___185_15090.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___185_15090.FStar_TypeChecker_Env.implicits)
            } in
          let uu____15091 =
            let uu____15092 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____15092 in
          if uu____15091
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15098 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____15098
                   then
                     let uu____15099 = FStar_TypeChecker_Env.get_range env in
                     let uu____15100 =
                       let uu____15101 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15101 in
                     FStar_Errors.diag uu____15099 uu____15100
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding] env vc in
                   let uu____15104 = check_trivial vc1 in
                   match uu____15104 with
                   | FStar_TypeChecker_Common.Trivial  -> Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then
                         ((let uu____15455 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15455
                           then
                             let uu____15456 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____15457 =
                               let uu____15458 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1
                                 "Cannot solve without SMT : %s\n"
                                 uu____15458 in
                             FStar_Errors.diag uu____15456 uu____15457
                           else ());
                          None)
                       else
                         ((let uu____15111 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15111
                           then
                             let uu____15112 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____15113 =
                               let uu____15114 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15114 in
                             FStar_Errors.diag uu____15112 uu____15113
                           else ());
                          (let vcs =
                             let uu____15120 = FStar_Options.use_tactics () in
                             if uu____15120
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else
                               (let uu____15479 =
                                  let uu____15483 = FStar_Options.peek () in
                                  (env, vc2, uu____15483) in
                                [uu____15479]) in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____15134  ->
                                   match uu____15134 with
                                   | (env1,goal) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify;
                                           FStar_TypeChecker_Normalize.Primops]
                                           env1 goal in
                                       let uu____15140 = check_trivial goal1 in
                                       (match uu____15140 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____15142 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____15142
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
                                             (let uu____15147 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____15147
                                              then
                                                let uu____15148 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____15149 =
                                                  let uu____15150 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____15151 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____15150 uu____15151 in
                                                FStar_Errors.diag uu____15148
                                                  uu____15149
                                              else ());
                                             (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                               use_env_range_msg env1 goal2;
                                             FStar_Options.pop ())))));
                          Some ret_g))))
let discharge_guard_no_smt:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15161 = discharge_guard' None env g false in
      match uu____15161 with
      | Some g1 -> g1
      | None  ->
          let uu____15166 =
            let uu____15167 =
              let uu____15170 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____15170) in
            FStar_Errors.Error uu____15167 in
          raise uu____15166
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15179 = discharge_guard' None env g true in
      match uu____15179 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits':
  Prims.bool ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun forcelax  ->
    fun g  ->
      let unresolved u =
        let uu____15565 = FStar_Syntax_Unionfind.find u in
        match uu____15565 with | None  -> true | uu____15567 -> false in
      let rec until_fixpoint acc implicits =
        let uu____15580 = acc in
        match uu____15580 with
        | (out,changed) ->
            (match implicits with
             | [] ->
                 if Prims.op_Negation changed
                 then out
                 else until_fixpoint ([], false) out
             | hd1::tl1 ->
                 let uu____15626 = hd1 in
                 (match uu____15626 with
                  | (uu____15633,env,u,tm,k,r) ->
                      let uu____15639 = unresolved u in
                      if uu____15639
                      then until_fixpoint ((hd1 :: out), changed) tl1
                      else
                        (let env1 =
                           FStar_TypeChecker_Env.set_expected_typ env k in
                         let tm1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta] env1 tm in
                         (let uu____15657 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "RelCheck") in
                          if uu____15657
                          then
                            let uu____15658 =
                              FStar_Syntax_Print.uvar_to_string u in
                            let uu____15659 =
                              FStar_Syntax_Print.term_to_string tm1 in
                            let uu____15660 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print3
                              "Checking uvar %s resolved to %s at type %s\n"
                              uu____15658 uu____15659 uu____15660
                          else ());
                         (let env2 =
                            if forcelax
                            then
                              let uu___185_15663 = env1 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___185_15663.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___185_15663.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___185_15663.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___185_15663.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___185_15663.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___185_15663.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___185_15663.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___185_15663.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___185_15663.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___185_15663.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___185_15663.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___185_15663.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___185_15663.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___185_15663.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___185_15663.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___185_15663.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___185_15663.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___185_15663.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___185_15663.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___185_15663.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___185_15663.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___185_15663.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___185_15663.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___185_15663.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___185_15663.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___185_15663.FStar_TypeChecker_Env.is_native_tactic)
                              }
                            else env1 in
                          let uu____15665 =
                            env2.FStar_TypeChecker_Env.type_of
                              (let uu___186_15669 = env2 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___186_15669.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___186_15669.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___186_15669.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___186_15669.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___186_15669.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___186_15669.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___186_15669.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___186_15669.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___186_15669.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___186_15669.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___186_15669.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___186_15669.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___186_15669.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___186_15669.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___186_15669.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___186_15669.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___186_15669.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___186_15669.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___186_15669.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___186_15669.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___186_15669.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___186_15669.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___186_15669.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___186_15669.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___186_15669.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___186_15669.FStar_TypeChecker_Env.is_native_tactic)
                               }) tm1 in
                          match uu____15665 with
                          | (uu____15670,uu____15671,g1) ->
                              let g2 =
                                if env2.FStar_TypeChecker_Env.is_pattern
                                then
                                  let uu___187_15674 = g1 in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      FStar_TypeChecker_Common.Trivial;
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___187_15674.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___187_15674.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits =
                                      (uu___187_15674.FStar_TypeChecker_Env.implicits)
                                  }
                                else g1 in
                              let g' =
                                let uu____15677 =
                                  discharge_guard'
                                    (Some
                                       (fun uu____15681  ->
                                          FStar_Syntax_Print.term_to_string
                                            tm1)) env2 g2 true in
                                match uu____15677 with
                                | Some g3 -> g3
                                | None  ->
                                    failwith
                                      "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                              until_fixpoint
                                ((FStar_List.append
                                    g'.FStar_TypeChecker_Env.implicits out),
                                  true) tl1)))) in
      let uu___188_15696 = g in
      let uu____15697 =
        until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___188_15696.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___188_15696.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs =
          (uu___188_15696.FStar_TypeChecker_Env.univ_ineqs);
        FStar_TypeChecker_Env.implicits = uu____15697
      }
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____15192 = FStar_Syntax_Unionfind.find u in
      match uu____15192 with | None  -> true | uu____15194 -> false in
    let rec until_fixpoint acc implicits =
      let uu____15207 = acc in
      match uu____15207 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____15253 = hd1 in
               (match uu____15253 with
                | (uu____15260,env,u,tm,k,r) ->
                    let uu____15266 = unresolved u in
                    if uu____15266
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm in
                       (let uu____15284 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck") in
                        if uu____15284
                        then
                          let uu____15285 =
                            FStar_Syntax_Print.uvar_to_string u in
                          let uu____15286 =
                            FStar_Syntax_Print.term_to_string tm1 in
                          let uu____15287 =
                            FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____15285 uu____15286 uu____15287
                        else ());
                       (let uu____15289 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___186_15293 = env1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___186_15293.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___186_15293.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___186_15293.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___186_15293.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___186_15293.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___186_15293.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___186_15293.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___186_15293.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___186_15293.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___186_15293.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___186_15293.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___186_15293.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___186_15293.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___186_15293.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___186_15293.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___186_15293.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___186_15293.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___186_15293.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___186_15293.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___186_15293.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___186_15293.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___186_15293.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___186_15293.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___186_15293.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___186_15293.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___186_15293.FStar_TypeChecker_Env.is_native_tactic)
                             }) tm1 in
                        match uu____15289 with
                        | (uu____15294,uu____15295,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___187_15298 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___187_15298.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___187_15298.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___187_15298.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____15301 =
                                discharge_guard'
                                  (Some
                                     (fun uu____15305  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____15301 with
                              | Some g3 -> g3
                              | None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
    let uu___188_15320 = g in
    let uu____15321 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___188_15320.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___188_15320.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___188_15320.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____15321
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____15351 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____15351 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15358 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15358
      | (reason,uu____15360,uu____15361,e,t,r)::uu____15365 ->
          let uu____15379 =
            let uu____15380 = FStar_Syntax_Print.term_to_string t in
            let uu____15381 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2
              "Failed to resolve implicit argument of type '%s' introduced in %s"
              uu____15380 uu____15381 in
          FStar_Errors.err r uu____15379
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___189_15390 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___189_15390.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___189_15390.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___189_15390.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15411 = try_teq false env t1 t2 in
        match uu____15411 with
        | None  -> false
        | Some g ->
            let uu____15414 = discharge_guard' None env g false in
            (match uu____15414 with
             | Some uu____15418 -> true
             | None  -> false)