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
            let uu___134_80 = g1 in
            let uu____81 =
              let uu____82 =
                let uu____83 =
                  let uu____84 = FStar_Syntax_Syntax.mk_binder x in
                  [uu____84] in
                let uu____85 =
                  let uu____92 =
                    let uu____98 =
                      let uu____99 =
                        FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                      FStar_All.pipe_right uu____99
                        FStar_Syntax_Util.lcomp_of_comp in
                    FStar_All.pipe_right uu____98
                      (fun _0_39  -> FStar_Util.Inl _0_39) in
                  Some uu____92 in
                FStar_Syntax_Util.abs uu____83 f uu____85 in
              FStar_All.pipe_left
                (fun _0_40  -> FStar_TypeChecker_Common.NonTrivial _0_40)
                uu____82 in
            {
              FStar_TypeChecker_Env.guard_f = uu____81;
              FStar_TypeChecker_Env.deferred =
                (uu___134_80.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___134_80.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___134_80.FStar_TypeChecker_Env.implicits)
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
          let uu___135_122 = g in
          let uu____123 =
            let uu____124 =
              let uu____125 =
                let uu____128 =
                  let uu____129 =
                    let uu____139 =
                      let uu____141 = FStar_Syntax_Syntax.as_arg e in
                      [uu____141] in
                    (f, uu____139) in
                  FStar_Syntax_Syntax.Tm_app uu____129 in
                FStar_Syntax_Syntax.mk uu____128 in
              uu____125
                (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun _0_41  -> FStar_TypeChecker_Common.NonTrivial _0_41)
              uu____124 in
          {
            FStar_TypeChecker_Env.guard_f = uu____123;
            FStar_TypeChecker_Env.deferred =
              (uu___135_122.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___135_122.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___135_122.FStar_TypeChecker_Env.implicits)
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
          let uu___136_165 = g in
          let uu____166 =
            let uu____167 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____167 in
          {
            FStar_TypeChecker_Env.guard_f = uu____166;
            FStar_TypeChecker_Env.deferred =
              (uu___136_165.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___136_165.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___136_165.FStar_TypeChecker_Env.implicits)
          }
let trivial: FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____172 -> failwith "impossible"
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
          let uu____185 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____185
let check_trivial:
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula =
  fun t  ->
    let uu____190 =
      let uu____191 = FStar_Syntax_Util.unmeta t in
      uu____191.FStar_Syntax_Syntax.n in
    match uu____190 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____195 -> FStar_TypeChecker_Common.NonTrivial t
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
        let uu____231 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
        {
          FStar_TypeChecker_Env.guard_f = uu____231;
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
                       let uu____283 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____283
                       then f1
                       else FStar_Syntax_Util.mk_forall u (fst b) f1) us bs f in
            let uu___137_285 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___137_285.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___137_285.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___137_285.FStar_TypeChecker_Env.implicits)
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
               let uu____302 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____302
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
            let uu___138_318 = g in
            let uu____319 =
              let uu____320 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____320 in
            {
              FStar_TypeChecker_Env.guard_f = uu____319;
              FStar_TypeChecker_Env.deferred =
                (uu___138_318.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___138_318.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___138_318.FStar_TypeChecker_Env.implicits)
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
        | uu____351 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____366 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____366 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                None r in
            let uu____378 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                (Some (k.FStar_Syntax_Syntax.n)) r in
            (uu____378, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____410 = FStar_Syntax_Util.type_u () in
        match uu____410 with
        | (t_type,u) ->
            let uu____415 =
              let uu____418 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____418 t_type in
            (match uu____415 with
             | (tt,uu____420) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of ((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
  FStar_Syntax_Syntax.term)
  | UNIV of (FStar_Syntax_Syntax.universe_uvar* FStar_Syntax_Syntax.universe)
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____444 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
      FStar_Syntax_Syntax.term)
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____472 -> false
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
    match projectee with | Success _0 -> true | uu____622 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____638 -> false
let __proj__Failed__item___0:
  solution -> (FStar_TypeChecker_Common.prob* Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0
type variance =
  | COVARIANT
  | CONTRAVARIANT
  | INVARIANT
let uu___is_COVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____657 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____662 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____667 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___106_685  ->
    match uu___106_685 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____701 =
    let uu____702 = FStar_Syntax_Subst.compress t in
    uu____702.FStar_Syntax_Syntax.n in
  match uu____701 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____719 = FStar_Syntax_Print.uvar_to_string u in
      let uu____720 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____719 uu____720
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____723;
         FStar_Syntax_Syntax.pos = uu____724;
         FStar_Syntax_Syntax.vars = uu____725;_},args)
      ->
      let uu____753 = FStar_Syntax_Print.uvar_to_string u in
      let uu____754 = FStar_Syntax_Print.term_to_string ty in
      let uu____755 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" uu____753 uu____754 uu____755
  | uu____756 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___107_764  ->
      match uu___107_764 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____768 =
            let uu____770 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____771 =
              let uu____773 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____774 =
                let uu____776 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____777 =
                  let uu____779 =
                    let uu____781 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____782 =
                      let uu____784 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____785 =
                        let uu____787 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (fst p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____788 =
                          let uu____790 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____790] in
                        uu____787 :: uu____788 in
                      uu____784 :: uu____785 in
                    uu____781 :: uu____782 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____779 in
                uu____776 :: uu____777 in
              uu____773 :: uu____774 in
            uu____770 :: uu____771 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____768
      | FStar_TypeChecker_Common.CProb p ->
          let uu____795 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____796 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____795
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____796
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___108_804  ->
      match uu___108_804 with
      | UNIV (u,t) ->
          let x =
            let uu____808 = FStar_Options.hide_uvar_nums () in
            if uu____808
            then "?"
            else
              (let uu____810 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____810 FStar_Util.string_of_int) in
          let uu____811 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____811
      | TERM ((u,uu____813),t) ->
          let x =
            let uu____818 = FStar_Options.hide_uvar_nums () in
            if uu____818
            then "?"
            else
              (let uu____820 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____820 FStar_Util.string_of_int) in
          let uu____821 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____821
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____832 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____832 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____841 =
      let uu____843 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____843
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____841 (FStar_String.concat ", ")
let args_to_string args =
  let uu____863 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____871  ->
            match uu____871 with
            | (x,uu____875) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right uu____863 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____881 =
      let uu____882 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____882 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____881;
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
        let uu___139_898 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___139_898.wl_deferred);
          ctr = (uu___139_898.ctr);
          defer_ok = (uu___139_898.defer_ok);
          smt_ok;
          tcenv = (uu___139_898.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___140_928 = empty_worklist env in
  let uu____929 = FStar_List.map FStar_Pervasives.snd g in
  {
    attempting = uu____929;
    wl_deferred = (uu___140_928.wl_deferred);
    ctr = (uu___140_928.ctr);
    defer_ok = false;
    smt_ok = (uu___140_928.smt_ok);
    tcenv = (uu___140_928.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___141_944 = wl in
        {
          attempting = (uu___141_944.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___141_944.ctr);
          defer_ok = (uu___141_944.defer_ok);
          smt_ok = (uu___141_944.smt_ok);
          tcenv = (uu___141_944.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___142_958 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___142_958.wl_deferred);
        ctr = (uu___142_958.ctr);
        defer_ok = (uu___142_958.defer_ok);
        smt_ok = (uu___142_958.smt_ok);
        tcenv = (uu___142_958.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____972 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____972
         then
           let uu____973 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____973
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___109_978  ->
    match uu___109_978 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___143_997 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___143_997.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___143_997.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___143_997.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___143_997.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___143_997.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___143_997.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___143_997.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___110_1022  ->
    match uu___110_1022 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_43  -> FStar_TypeChecker_Common.CProb _0_43)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___111_1040  ->
      match uu___111_1040 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___112_1044  ->
    match uu___112_1044 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___113_1054  ->
    match uu___113_1054 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___114_1065  ->
    match uu___114_1065 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___115_1076  ->
    match uu___115_1076 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun uu___116_1088  ->
    match uu___116_1088 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___117_1100  ->
    match uu___117_1100 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___118_1110  ->
    match uu___118_1110 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.TProb _0_44) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_45  -> FStar_TypeChecker_Common.CProb _0_45) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____1125 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1125 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1141  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1200 = next_pid () in
  let uu____1201 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1200;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1201;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1257 = next_pid () in
  let uu____1258 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1257;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1258;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1307 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1307;
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
        let uu____1367 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1367
        then
          let uu____1368 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1369 = prob_to_string env d in
          let uu____1370 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1368 uu____1369 uu____1370 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1375 -> failwith "impossible" in
           let uu____1376 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1384 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1385 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1384, uu____1385)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1389 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1390 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1389, uu____1390) in
           match uu____1376 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___119_1400  ->
            match uu___119_1400 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1406 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1408),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___120_1423  ->
           match uu___120_1423 with
           | UNIV uu____1425 -> None
           | TERM ((u,uu____1429),t) ->
               let uu____1433 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1433 then Some t else None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___121_1447  ->
           match uu___121_1447 with
           | UNIV (u',t) ->
               let uu____1451 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1451 then Some t else None
           | uu____1454 -> None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1463 =
        let uu____1464 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1464 in
      FStar_Syntax_Subst.compress uu____1463
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1473 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1473
let norm_arg env t = let uu____1495 = sn env (fst t) in (uu____1495, (snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1514  ->
              match uu____1514 with
              | (x,imp) ->
                  let uu____1521 =
                    let uu___144_1522 = x in
                    let uu____1523 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___144_1522.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___144_1522.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1523
                    } in
                  (uu____1521, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1540 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1540
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1543 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1543
        | uu____1545 -> u2 in
      let uu____1546 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1546
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1662 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____1662 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1674;
               FStar_Syntax_Syntax.pos = uu____1675;
               FStar_Syntax_Syntax.vars = uu____1676;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1697 =
                 let uu____1698 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1699 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1698
                   uu____1699 in
               failwith uu____1697)
    | FStar_Syntax_Syntax.Tm_uinst uu____1709 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1736 =
             let uu____1737 = FStar_Syntax_Subst.compress t1' in
             uu____1737.FStar_Syntax_Syntax.n in
           match uu____1736 with
           | FStar_Syntax_Syntax.Tm_refine uu____1749 -> aux true t1'
           | uu____1754 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1766 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1789 =
             let uu____1790 = FStar_Syntax_Subst.compress t1' in
             uu____1790.FStar_Syntax_Syntax.n in
           match uu____1789 with
           | FStar_Syntax_Syntax.Tm_refine uu____1802 -> aux true t1'
           | uu____1807 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_app uu____1819 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1851 =
             let uu____1852 = FStar_Syntax_Subst.compress t1' in
             uu____1852.FStar_Syntax_Syntax.n in
           match uu____1851 with
           | FStar_Syntax_Syntax.Tm_refine uu____1864 -> aux true t1'
           | uu____1869 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_type uu____1881 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_constant uu____1893 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_name uu____1905 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1917 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1929 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_abs uu____1948 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1974 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_let uu____1994 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_match uu____2013 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_meta uu____2040 ->
        let uu____2045 =
          let uu____2046 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2047 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2046
            uu____2047 in
        failwith uu____2045
    | FStar_Syntax_Syntax.Tm_ascribed uu____2057 ->
        let uu____2075 =
          let uu____2076 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2077 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2076
            uu____2077 in
        failwith uu____2075
    | FStar_Syntax_Syntax.Tm_delayed uu____2087 ->
        let uu____2108 =
          let uu____2109 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2110 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2109
            uu____2110 in
        failwith uu____2108
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____2120 =
          let uu____2121 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2122 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2121
            uu____2122 in
        failwith uu____2120 in
  let uu____2132 = whnf env t1 in aux false uu____2132
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____2143 =
        let uu____2153 = empty_worklist env in
        base_and_refinement env uu____2153 t in
      FStar_All.pipe_right uu____2143 FStar_Pervasives.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____2178 = FStar_Syntax_Syntax.null_bv t in
    (uu____2178, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____2202 = base_and_refinement env wl t in
  match uu____2202 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
let force_refinement uu____2263 =
  match uu____2263 with
  | (t_base,refopt) ->
      let uu____2277 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base in
      (match uu____2277 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___122_2303  ->
      match uu___122_2303 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2307 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2308 =
            let uu____2309 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____2309 in
          let uu____2310 =
            let uu____2311 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____2311 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2307 uu____2308
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2310
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2315 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2316 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____2317 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2315 uu____2316
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2317
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2322 =
      let uu____2324 =
        let uu____2326 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2336  ->
                  match uu____2336 with | (uu____2340,uu____2341,x) -> x)) in
        FStar_List.append wl.attempting uu____2326 in
      FStar_List.map (wl_prob_to_string wl) uu____2324 in
    FStar_All.pipe_right uu____2322 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
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
                 | (ys',t1,uu____2453) ->
                     let uu____2466 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2466))
          | uu____2487 ->
              let uu____2488 =
                let uu____2494 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____2494) in
              ((ys, t), uu____2488) in
        match uu____2362 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2553 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2553 c in
               let uu____2555 =
                 let uu____2562 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_46  -> FStar_Util.Inl _0_46) in
                 FStar_All.pipe_right uu____2562 (fun _0_47  -> Some _0_47) in
               FStar_Syntax_Util.abs ys1 t1 uu____2555)
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
            let uu____2618 = p_guard prob in
            match uu____2618 with
            | (uu____2621,uv) ->
                ((let uu____2624 =
                    let uu____2625 = FStar_Syntax_Subst.compress uv in
                    uu____2625.FStar_Syntax_Syntax.n in
                  match uu____2624 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2645 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2645
                        then
                          let uu____2646 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2647 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2648 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2646
                            uu____2647 uu____2648
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2650 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___145_2653 = wl in
                  {
                    attempting = (uu___145_2653.attempting);
                    wl_deferred = (uu___145_2653.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___145_2653.defer_ok);
                    smt_ok = (uu___145_2653.smt_ok);
                    tcenv = (uu___145_2653.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2669 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2669
         then
           let uu____2670 = FStar_Util.string_of_int pid in
           let uu____2671 =
             let uu____2672 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2672 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2670 uu____2671
         else ());
        commit sol;
        (let uu___146_2677 = wl in
         {
           attempting = (uu___146_2677.attempting);
           wl_deferred = (uu___146_2677.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___146_2677.defer_ok);
           smt_ok = (uu___146_2677.smt_ok);
           tcenv = (uu___146_2677.tcenv)
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
            | (uu____2710,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2718 = FStar_Syntax_Util.mk_conj t1 f in
                Some uu____2718 in
          (let uu____2724 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2724
           then
             let uu____2725 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2726 =
               let uu____2727 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2727 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2725 uu____2726
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2756 =
    let uu____2760 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2760 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2756
    (FStar_Util.for_some
       (fun uu____2777  ->
          match uu____2777 with
          | (uv,uu____2781) -> FStar_Syntax_Unionfind.equiv uv (fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2820 = occurs wl uk t in Prims.op_Negation uu____2820 in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2825 =
         let uu____2826 = FStar_Syntax_Print.uvar_to_string (fst uk) in
         let uu____2827 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2826 uu____2827 in
       Some uu____2825) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2882 = occurs_check env wl uk t in
  match uu____2882 with
  | (occurs_ok,msg) ->
      let uu____2899 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2899, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2967 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2991  ->
            fun uu____2992  ->
              match (uu____2991, uu____2992) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____3035 =
                    let uu____3036 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____3036 in
                  if uu____3035
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____3050 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____3050
                     then
                       let uu____3057 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____3057)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2967 with | (isect,uu____3079) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____3136  ->
          fun uu____3137  ->
            match (uu____3136, uu____3137) with
            | ((a,uu____3147),(b,uu____3149)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____3198 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____3204  ->
                match uu____3204 with
                | (b,uu____3208) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____3198 then None else Some (a, (snd hd1))
  | uu____3217 -> None
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
            let uu____3263 = pat_var_opt env seen hd1 in
            (match uu____3263 with
             | None  ->
                 ((let uu____3271 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____3271
                   then
                     let uu____3272 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____3272
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3285 =
      let uu____3286 = FStar_Syntax_Subst.compress t in
      uu____3286.FStar_Syntax_Syntax.n in
    match uu____3285 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3289 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3298;
           FStar_Syntax_Syntax.tk = uu____3299;
           FStar_Syntax_Syntax.pos = uu____3300;
           FStar_Syntax_Syntax.vars = uu____3301;_},uu____3302)
        -> true
    | uu____3325 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3389;
         FStar_Syntax_Syntax.pos = uu____3390;
         FStar_Syntax_Syntax.vars = uu____3391;_},args)
      -> (t, uv, k, args)
  | uu____3432 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____3489 = destruct_flex_t t in
  match uu____3489 with
  | (t1,uv,k,args) ->
      let uu____3557 = pat_vars env [] args in
      (match uu____3557 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3613 -> ((t1, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth option*
  FStar_Syntax_Syntax.delta_depth option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3663 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth option* FStar_Syntax_Syntax.delta_depth
      option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3688 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3693 -> false
let head_match: match_result -> match_result =
  fun uu___123_3697  ->
    match uu___123_3697 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3706 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3721 ->
          let uu____3722 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3722 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3732 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3748 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3754 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> None
      | FStar_Syntax_Syntax.Tm_bvar uu____3776 -> None
      | FStar_Syntax_Syntax.Tm_name uu____3777 -> None
      | FStar_Syntax_Syntax.Tm_uvar uu____3778 -> None
      | FStar_Syntax_Syntax.Tm_let uu____3787 -> None
      | FStar_Syntax_Syntax.Tm_match uu____3795 -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3812) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3818,uu____3819) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3849) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3864;
             FStar_Syntax_Syntax.index = uu____3865;
             FStar_Syntax_Syntax.sort = t2;_},uu____3867)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3874 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3875 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3876 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3884 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3900 = fv_delta_depth env fv in Some uu____3900
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
            let uu____3922 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3922
            then FullMatch
            else
              (let uu____3924 =
                 let uu____3929 =
                   let uu____3931 = fv_delta_depth env f in Some uu____3931 in
                 let uu____3932 =
                   let uu____3934 = fv_delta_depth env g in Some uu____3934 in
                 (uu____3929, uu____3932) in
               MisMatch uu____3924)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3938),FStar_Syntax_Syntax.Tm_uinst (g,uu____3940)) ->
            let uu____3949 = head_matches env f g in
            FStar_All.pipe_right uu____3949 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3956),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3958)) ->
            let uu____3983 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____3983 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3988),FStar_Syntax_Syntax.Tm_refine (y,uu____3990)) ->
            let uu____3999 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3999 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____4001),uu____4002) ->
            let uu____4007 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____4007 head_match
        | (uu____4008,FStar_Syntax_Syntax.Tm_refine (x,uu____4010)) ->
            let uu____4015 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____4015 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____4016,FStar_Syntax_Syntax.Tm_type
           uu____4017) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____4018,FStar_Syntax_Syntax.Tm_arrow uu____4019) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____4035),FStar_Syntax_Syntax.Tm_app (head',uu____4037))
            ->
            let uu____4066 = head_matches env head1 head' in
            FStar_All.pipe_right uu____4066 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____4068),uu____4069) ->
            let uu____4084 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____4084 head_match
        | (uu____4085,FStar_Syntax_Syntax.Tm_app (head1,uu____4087)) ->
            let uu____4102 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____4102 head_match
        | uu____4103 ->
            let uu____4106 =
              let uu____4111 = delta_depth_of_term env t11 in
              let uu____4113 = delta_depth_of_term env t21 in
              (uu____4111, uu____4113) in
            MisMatch uu____4106
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____4154 = FStar_Syntax_Util.head_and_args t in
    match uu____4154 with
    | (head1,uu____4166) ->
        let uu____4181 =
          let uu____4182 = FStar_Syntax_Util.un_uinst head1 in
          uu____4182.FStar_Syntax_Syntax.n in
        (match uu____4181 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____4187 =
               let uu____4188 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____4188 FStar_Option.isSome in
             if uu____4187
             then
               let uu____4202 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____4202 (fun _0_48  -> Some _0_48)
             else None
         | uu____4205 -> None) in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None)) in
  let fail r = (r, None) in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21 in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),uu____4273) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4283 =
             let uu____4288 = maybe_inline t11 in
             let uu____4290 = maybe_inline t21 in (uu____4288, uu____4290) in
           match uu____4283 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (uu____4311,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4321 =
             let uu____4326 = maybe_inline t11 in
             let uu____4328 = maybe_inline t21 in (uu____4326, uu____4328) in
           match uu____4321 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____4353 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____4353 with
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
        let uu____4368 =
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
        (match uu____4368 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4383 -> fail r
    | uu____4388 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4418 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4450 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4468 = FStar_Syntax_Util.type_u () in
      match uu____4468 with
      | (t,uu____4472) ->
          let uu____4473 = new_uvar r binders t in fst uu____4473
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4484 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____4484 FStar_Pervasives.fst
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
        let uu____4528 = head_matches env t1 t' in
        match uu____4528 with
        | MisMatch uu____4529 -> false
        | uu____4534 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4594,imp),T (t2,uu____4597)) -> (t2, imp)
                     | uu____4614 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4654  ->
                    match uu____4654 with
                    | (t2,uu____4662) ->
                        (None, INVARIANT, (T (t2, generic_kind))))) in
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
                         (((let uu___147_4767 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___147_4767.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___147_4767.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4777 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___124_4808 =
                 match uu___124_4808 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4871 = decompose1 [] bs1 in
               (rebuild, matches, uu____4871))
      | uu____4899 ->
          let rebuild uu___125_4904 =
            match uu___125_4904 with
            | [] -> t1
            | uu____4906 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___126_4926  ->
    match uu___126_4926 with
    | T (t,uu____4928) -> t
    | uu____4937 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___127_4941  ->
    match uu___127_4941 with
    | T (t,uu____4943) -> FStar_Syntax_Syntax.as_arg t
    | uu____4952 -> failwith "Impossible"
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
              | (uu____5026,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____5045 = new_uvar r scope1 k in
                  (match uu____5045 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____5057 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args)) None r in
                       let uu____5072 =
                         let uu____5073 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_49  ->
                              FStar_TypeChecker_Common.TProb _0_49)
                           uu____5073 in
                       ((T (gi_xs, mk_kind)), uu____5072))
              | (uu____5082,uu____5083,C uu____5084) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____5171 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____5182;
                         FStar_Syntax_Syntax.pos = uu____5183;
                         FStar_Syntax_Syntax.vars = uu____5184;_})
                        ->
                        let uu____5199 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____5199 with
                         | (T (gi_xs,uu____5215),prob) ->
                             let uu____5225 =
                               let uu____5226 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_50  -> C _0_50)
                                 uu____5226 in
                             (uu____5225, [prob])
                         | uu____5228 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____5238;
                         FStar_Syntax_Syntax.pos = uu____5239;
                         FStar_Syntax_Syntax.vars = uu____5240;_})
                        ->
                        let uu____5255 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____5255 with
                         | (T (gi_xs,uu____5271),prob) ->
                             let uu____5281 =
                               let uu____5282 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_51  -> C _0_51)
                                 uu____5282 in
                             (uu____5281, [prob])
                         | uu____5284 -> failwith "impossible")
                    | (uu____5290,uu____5291,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____5293;
                         FStar_Syntax_Syntax.pos = uu____5294;
                         FStar_Syntax_Syntax.vars = uu____5295;_})
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
                        let uu____5369 =
                          let uu____5374 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____5374 FStar_List.unzip in
                        (match uu____5369 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5403 =
                                 let uu____5404 =
                                   let uu____5407 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____5407 un_T in
                                 let uu____5408 =
                                   let uu____5414 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____5414
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5404;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5408;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5403 in
                             ((C gi_xs), sub_probs))
                    | uu____5419 ->
                        let uu____5426 = sub_prob scope1 args q in
                        (match uu____5426 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____5171 with
                   | (tc,probs) ->
                       let uu____5444 =
                         match q with
                         | (Some b,uu____5470,uu____5471) ->
                             let uu____5479 =
                               let uu____5483 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____5483 :: args in
                             ((Some b), (b :: scope1), uu____5479)
                         | uu____5501 -> (None, scope1, args) in
                       (match uu____5444 with
                        | (bopt,scope2,args1) ->
                            let uu____5544 = aux scope2 args1 qs2 in
                            (match uu____5544 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____5565 =
                                         let uu____5567 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         f :: uu____5567 in
                                       FStar_Syntax_Util.mk_conj_l uu____5565
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (fst b).FStar_Syntax_Syntax.sort in
                                       let uu____5580 =
                                         let uu____5582 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (fst b) f in
                                         let uu____5583 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         uu____5582 :: uu____5583 in
                                       FStar_Syntax_Util.mk_conj_l uu____5580 in
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
  let uu___148_5639 = p in
  let uu____5642 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____5643 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___148_5639.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5642;
    FStar_TypeChecker_Common.relation =
      (uu___148_5639.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5643;
    FStar_TypeChecker_Common.element =
      (uu___148_5639.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___148_5639.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___148_5639.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___148_5639.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___148_5639.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___148_5639.FStar_TypeChecker_Common.rank)
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
            (fun _0_52  -> FStar_TypeChecker_Common.TProb _0_52)
      | FStar_TypeChecker_Common.CProb uu____5660 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
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
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5767,uu____5768)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5779,FStar_Syntax_Syntax.Tm_uvar uu____5780)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5791,uu____5792)
                          ->
                          let uu____5801 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5801 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5841 ->
                                    let rank =
                                      let uu____5848 = is_top_level_prob prob in
                                      if uu____5848
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5850 =
                                      let uu___149_5853 = tp in
                                      let uu____5856 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_5853.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___149_5853.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_5853.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5856;
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_5853.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_5853.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_5853.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_5853.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_5853.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_5853.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5850)))
                      | (uu____5866,FStar_Syntax_Syntax.Tm_uvar uu____5867)
                          ->
                          let uu____5876 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5876 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5916 ->
                                    let uu____5922 =
                                      let uu___150_5927 = tp in
                                      let uu____5930 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___150_5927.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5930;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___150_5927.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___150_5927.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___150_5927.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___150_5927.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___150_5927.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___150_5927.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___150_5927.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___150_5927.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5922)))
                      | (uu____5946,uu____5947) -> (rigid_rigid, tp) in
                    (match uu____5738 with
                     | (rank,tp1) ->
                         let uu____5958 =
                           FStar_All.pipe_right
                             (let uu___151_5961 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___151_5961.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___151_5961.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___151_5961.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___151_5961.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___151_5961.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___151_5961.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___151_5961.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___151_5961.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___151_5961.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_53  ->
                                FStar_TypeChecker_Common.TProb _0_53) in
                         (rank, uu____5958))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5967 =
            FStar_All.pipe_right
              (let uu___152_5970 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___152_5970.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___152_5970.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___152_5970.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___152_5970.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___152_5970.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___152_5970.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___152_5970.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___152_5970.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___152_5970.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_54  -> FStar_TypeChecker_Common.CProb _0_54) in
          (rigid_rigid, uu____5967)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob option* FStar_TypeChecker_Common.prob
      Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____6003 probs =
      match uu____6003 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____6033 = rank wl hd1 in
               (match uu____6033 with
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
    match projectee with | UDeferred _0 -> true | uu____6104 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____6118 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____6132 -> false
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
                        let uu____6170 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____6170 with
                        | (k,uu____6174) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____6178 -> false)))
            | uu____6179 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____6226 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____6226 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____6229 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____6235 =
                     let uu____6236 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____6237 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____6236
                       uu____6237 in
                   UFailed uu____6235)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____6253 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____6253 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____6271 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____6271 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____6274 ->
                let uu____6277 =
                  let uu____6278 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____6279 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____6278
                    uu____6279 msg in
                UFailed uu____6277 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____6280,uu____6281) ->
              let uu____6282 =
                let uu____6283 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6284 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6283 uu____6284 in
              failwith uu____6282
          | (FStar_Syntax_Syntax.U_unknown ,uu____6285) ->
              let uu____6286 =
                let uu____6287 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6288 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6287 uu____6288 in
              failwith uu____6286
          | (uu____6289,FStar_Syntax_Syntax.U_bvar uu____6290) ->
              let uu____6291 =
                let uu____6292 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6293 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6292 uu____6293 in
              failwith uu____6291
          | (uu____6294,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____6295 =
                let uu____6296 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6297 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6296 uu____6297 in
              failwith uu____6295
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____6309 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____6309
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____6319 = occurs_univ v1 u3 in
              if uu____6319
              then
                let uu____6320 =
                  let uu____6321 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6322 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6321 uu____6322 in
                try_umax_components u11 u21 uu____6320
              else
                (let uu____6324 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6324)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
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
          | (FStar_Syntax_Syntax.U_max uu____6340,uu____6341) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6346 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6346
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____6348,FStar_Syntax_Syntax.U_max uu____6349) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6354 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6354
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6356,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6357,FStar_Syntax_Syntax.U_name
             uu____6358) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6359) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6360) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6361,FStar_Syntax_Syntax.U_succ
             uu____6362) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6363,FStar_Syntax_Syntax.U_zero
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
  let uu____6433 = bc1 in
  match uu____6433 with
  | (bs1,mk_cod1) ->
      let uu____6458 = bc2 in
      (match uu____6458 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6505 = FStar_Util.first_N n1 bs in
             match uu____6505 with
             | (bs3,rest) ->
                 let uu____6519 = mk_cod rest in (bs3, uu____6519) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____6543 =
               let uu____6547 = mk_cod1 [] in (bs1, uu____6547) in
             let uu____6549 =
               let uu____6553 = mk_cod2 [] in (bs2, uu____6553) in
             (uu____6543, uu____6549)
           else
             if l1 > l2
             then
               (let uu____6580 = curry l2 bs1 mk_cod1 in
                let uu____6590 =
                  let uu____6594 = mk_cod2 [] in (bs2, uu____6594) in
                (uu____6580, uu____6590))
             else
               (let uu____6603 =
                  let uu____6607 = mk_cod1 [] in (bs1, uu____6607) in
                let uu____6609 = curry l1 bs2 mk_cod2 in
                (uu____6603, uu____6609)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6716 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____6716
       then
         let uu____6717 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6717
       else ());
      (let uu____6719 = next_prob probs in
       match uu____6719 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___153_6732 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___153_6732.wl_deferred);
               ctr = (uu___153_6732.ctr);
               defer_ok = (uu___153_6732.defer_ok);
               smt_ok = (uu___153_6732.smt_ok);
               tcenv = (uu___153_6732.tcenv)
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
                  let uu____6739 = solve_flex_rigid_join env tp probs1 in
                  (match uu____6739 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6743 = solve_rigid_flex_meet env tp probs1 in
                     match uu____6743 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____6747,uu____6748) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6757 ->
                let uu____6762 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6790  ->
                          match uu____6790 with
                          | (c,uu____6795,uu____6796) -> c < probs.ctr)) in
                (match uu____6762 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6818 =
                            FStar_List.map
                              (fun uu____6824  ->
                                 match uu____6824 with
                                 | (uu____6830,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____6818
                      | uu____6833 ->
                          let uu____6838 =
                            let uu___154_6839 = probs in
                            let uu____6840 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6849  ->
                                      match uu____6849 with
                                      | (uu____6853,uu____6854,y) -> y)) in
                            {
                              attempting = uu____6840;
                              wl_deferred = rest;
                              ctr = (uu___154_6839.ctr);
                              defer_ok = (uu___154_6839.defer_ok);
                              smt_ok = (uu___154_6839.smt_ok);
                              tcenv = (uu___154_6839.tcenv)
                            } in
                          solve env uu____6838))))
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
            let uu____6861 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____6861 with
            | USolved wl1 ->
                let uu____6863 = solve_prob orig None [] wl1 in
                solve env uu____6863
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
                  let uu____6897 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6897 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6900 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6908;
                  FStar_Syntax_Syntax.pos = uu____6909;
                  FStar_Syntax_Syntax.vars = uu____6910;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6913;
                  FStar_Syntax_Syntax.pos = uu____6914;
                  FStar_Syntax_Syntax.vars = uu____6915;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6927,uu____6928) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6933,FStar_Syntax_Syntax.Tm_uinst uu____6934) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6939 -> USolved wl
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
            ((let uu____6947 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6947
              then
                let uu____6948 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6948 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6956 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6956
         then
           let uu____6957 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6957
         else ());
        (let uu____6959 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6959 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____7001 = head_matches_delta env () t1 t2 in
               match uu____7001 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____7023 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____7049 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____7058 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____7059 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____7058, uu____7059)
                          | None  ->
                              let uu____7062 = FStar_Syntax_Subst.compress t1 in
                              let uu____7063 = FStar_Syntax_Subst.compress t2 in
                              (uu____7062, uu____7063) in
                        (match uu____7049 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____7085 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_55  ->
                                    FStar_TypeChecker_Common.TProb _0_55)
                                 uu____7085 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____7108 =
                                    let uu____7114 =
                                      let uu____7117 =
                                        let uu____7120 =
                                          let uu____7121 =
                                            let uu____7126 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____7126) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____7121 in
                                        FStar_Syntax_Syntax.mk uu____7120 in
                                      uu____7117 None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____7139 =
                                      let uu____7141 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____7141] in
                                    (uu____7114, uu____7139) in
                                  Some uu____7108
                              | (uu____7150,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____7152)) ->
                                  let uu____7157 =
                                    let uu____7161 =
                                      let uu____7163 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____7163] in
                                    (t11, uu____7161) in
                                  Some uu____7157
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____7169),uu____7170) ->
                                  let uu____7175 =
                                    let uu____7179 =
                                      let uu____7181 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____7181] in
                                    (t21, uu____7179) in
                                  Some uu____7175
                              | uu____7186 ->
                                  let uu____7189 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____7189 with
                                   | (head1,uu____7204) ->
                                       let uu____7219 =
                                         let uu____7220 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____7220.FStar_Syntax_Syntax.n in
                                       (match uu____7219 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____7227;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____7229;_}
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
                                        | uu____7238 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7247) ->
                  let uu____7260 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___128_7269  ->
                            match uu___128_7269 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____7274 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____7274 with
                                      | (u',uu____7285) ->
                                          let uu____7300 =
                                            let uu____7301 = whnf env u' in
                                            uu____7301.FStar_Syntax_Syntax.n in
                                          (match uu____7300 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____7305) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____7318 -> false))
                                 | uu____7319 -> false)
                            | uu____7321 -> false)) in
                  (match uu____7260 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____7342 tps =
                         match uu____7342 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7369 =
                                    let uu____7374 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____7374 in
                                  (match uu____7369 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____7393 -> None) in
                       let uu____7398 =
                         let uu____7403 =
                           let uu____7407 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____7407, []) in
                         make_lower_bound uu____7403 lower_bounds in
                       (match uu____7398 with
                        | None  ->
                            ((let uu____7414 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7414
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
                            ((let uu____7427 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7427
                              then
                                let wl' =
                                  let uu___155_7429 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___155_7429.wl_deferred);
                                    ctr = (uu___155_7429.ctr);
                                    defer_ok = (uu___155_7429.defer_ok);
                                    smt_ok = (uu___155_7429.smt_ok);
                                    tcenv = (uu___155_7429.tcenv)
                                  } in
                                let uu____7430 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7430
                              else ());
                             (let uu____7432 =
                                solve_t env eq_prob
                                  (let uu___156_7433 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___156_7433.wl_deferred);
                                     ctr = (uu___156_7433.ctr);
                                     defer_ok = (uu___156_7433.defer_ok);
                                     smt_ok = (uu___156_7433.smt_ok);
                                     tcenv = (uu___156_7433.tcenv)
                                   }) in
                              match uu____7432 with
                              | Success uu____7435 ->
                                  let wl1 =
                                    let uu___157_7437 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___157_7437.wl_deferred);
                                      ctr = (uu___157_7437.ctr);
                                      defer_ok = (uu___157_7437.defer_ok);
                                      smt_ok = (uu___157_7437.smt_ok);
                                      tcenv = (uu___157_7437.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1 in
                                  let uu____7439 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds in
                                  Some wl2
                              | uu____7442 -> None))))
              | uu____7443 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7450 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____7450
         then
           let uu____7451 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7451
         else ());
        (let uu____7453 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____7453 with
         | (u,args) ->
             let uu____7480 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____7480 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____7511 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____7511 with
                    | (h1,args1) ->
                        let uu____7539 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____7539 with
                         | (h2,uu____7552) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7571 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____7571
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7586 =
                                          let uu____7588 =
                                            let uu____7589 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_56  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_56) uu____7589 in
                                          [uu____7588] in
                                        Some uu____7586))
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
                                       (let uu____7613 =
                                          let uu____7615 =
                                            let uu____7616 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_57  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_57) uu____7616 in
                                          [uu____7615] in
                                        Some uu____7613))
                                  else None
                              | uu____7624 -> None)) in
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
                             let uu____7690 =
                               let uu____7696 =
                                 let uu____7699 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____7699 in
                               (uu____7696, m1) in
                             Some uu____7690)
                    | (uu____7708,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7710)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7742),uu____7743) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____7774 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7808) ->
                       let uu____7821 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___129_7830  ->
                                 match uu___129_7830 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____7835 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____7835 with
                                           | (u',uu____7846) ->
                                               let uu____7861 =
                                                 let uu____7862 = whnf env u' in
                                                 uu____7862.FStar_Syntax_Syntax.n in
                                               (match uu____7861 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7866) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____7879 -> false))
                                      | uu____7880 -> false)
                                 | uu____7882 -> false)) in
                       (match uu____7821 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7907 tps =
                              match uu____7907 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7948 =
                                         let uu____7955 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7955 in
                                       (match uu____7948 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7990 -> None) in
                            let uu____7997 =
                              let uu____8004 =
                                let uu____8010 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____8010, []) in
                              make_upper_bound uu____8004 upper_bounds in
                            (match uu____7997 with
                             | None  ->
                                 ((let uu____8019 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____8019
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
                                 ((let uu____8038 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____8038
                                   then
                                     let wl' =
                                       let uu___158_8040 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___158_8040.wl_deferred);
                                         ctr = (uu___158_8040.ctr);
                                         defer_ok = (uu___158_8040.defer_ok);
                                         smt_ok = (uu___158_8040.smt_ok);
                                         tcenv = (uu___158_8040.tcenv)
                                       } in
                                     let uu____8041 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____8041
                                   else ());
                                  (let uu____8043 =
                                     solve_t env eq_prob
                                       (let uu___159_8044 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___159_8044.wl_deferred);
                                          ctr = (uu___159_8044.ctr);
                                          defer_ok = (uu___159_8044.defer_ok);
                                          smt_ok = (uu___159_8044.smt_ok);
                                          tcenv = (uu___159_8044.tcenv)
                                        }) in
                                   match uu____8043 with
                                   | Success uu____8046 ->
                                       let wl1 =
                                         let uu___160_8048 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___160_8048.wl_deferred);
                                           ctr = (uu___160_8048.ctr);
                                           defer_ok =
                                             (uu___160_8048.defer_ok);
                                           smt_ok = (uu___160_8048.smt_ok);
                                           tcenv = (uu___160_8048.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1 in
                                       let uu____8050 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds in
                                       Some wl2
                                   | uu____8053 -> None))))
                   | uu____8054 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____8119 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____8119
                      then
                        let uu____8120 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____8120
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___161_8152 = hd1 in
                      let uu____8153 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_8152.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_8152.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____8153
                      } in
                    let hd21 =
                      let uu___162_8157 = hd2 in
                      let uu____8158 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___162_8157.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___162_8157.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____8158
                      } in
                    let prob =
                      let uu____8162 =
                        let uu____8165 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____8165 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_58  -> FStar_TypeChecker_Common.TProb _0_58)
                        uu____8162 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____8173 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____8173 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____8176 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____8176 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____8194 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives.fst in
                           let uu____8197 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____8194 uu____8197 in
                         ((let uu____8203 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____8203
                           then
                             let uu____8204 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____8205 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____8204 uu____8205
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____8220 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____8226 = aux scope env [] bs1 bs2 in
              match uu____8226 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____8242 = compress_tprob wl problem in
        solve_t' env uu____8242 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____8275 = head_matches_delta env1 wl1 t1 t2 in
          match uu____8275 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____8292,uu____8293) ->
                   let may_relate head3 =
                     let uu____8308 =
                       let uu____8309 = FStar_Syntax_Util.un_uinst head3 in
                       uu____8309.FStar_Syntax_Syntax.n in
                     match uu____8308 with
                     | FStar_Syntax_Syntax.Tm_name uu____8312 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____8313 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____8330 -> false in
                   let uu____8331 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____8331
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
                                let uu____8348 =
                                  let uu____8349 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____8349 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____8348 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____8351 = solve_prob orig (Some guard) [] wl1 in
                     solve env1 uu____8351
                   else
                     (let uu____8353 =
                        let uu____8354 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____8355 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____8354 uu____8355 in
                      giveup env1 uu____8353 orig)
               | (uu____8356,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___163_8364 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___163_8364.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___163_8364.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___163_8364.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___163_8364.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___163_8364.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___163_8364.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___163_8364.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___163_8364.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____8365,None ) ->
                   ((let uu____8372 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8372
                     then
                       let uu____8373 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____8374 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____8375 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____8376 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____8373
                         uu____8374 uu____8375 uu____8376
                     else ());
                    (let uu____8378 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____8378 with
                     | (head11,args1) ->
                         let uu____8404 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____8404 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8449 =
                                  let uu____8450 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____8451 = args_to_string args1 in
                                  let uu____8452 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____8453 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8450 uu____8451 uu____8452
                                    uu____8453 in
                                giveup env1 uu____8449 orig
                              else
                                (let uu____8455 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8460 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____8460 = FStar_Syntax_Util.Equal) in
                                 if uu____8455
                                 then
                                   let uu____8461 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____8461 with
                                   | USolved wl2 ->
                                       let uu____8463 =
                                         solve_prob orig None [] wl2 in
                                       solve env1 uu____8463
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8467 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____8467 with
                                    | (base1,refinement1) ->
                                        let uu____8493 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____8493 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____8547 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____8547 with
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
                                                           (fun uu____8557 
                                                              ->
                                                              fun uu____8558 
                                                                ->
                                                                match 
                                                                  (uu____8557,
                                                                    uu____8558)
                                                                with
                                                                | ((a,uu____8568),
                                                                   (a',uu____8570))
                                                                    ->
                                                                    let uu____8575
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
                                                                    _0_59  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_59)
                                                                    uu____8575)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____8581 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8581 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8585 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___164_8618 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___164_8618.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___164_8618.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___164_8618.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___164_8618.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___164_8618.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___164_8618.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___164_8618.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___164_8618.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____8638 = p in
          match uu____8638 with
          | (((u,k),xs,c),ps,(h,uu____8649,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8698 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____8698 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8712 = h gs_xs in
                     let uu____8713 =
                       let uu____8720 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_60  -> FStar_Util.Inl _0_60) in
                       FStar_All.pipe_right uu____8720
                         (fun _0_61  -> Some _0_61) in
                     FStar_Syntax_Util.abs xs1 uu____8712 uu____8713 in
                   ((let uu____8751 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8751
                     then
                       let uu____8752 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____8753 = FStar_Syntax_Print.comp_to_string c in
                       let uu____8754 = FStar_Syntax_Print.term_to_string im in
                       let uu____8755 = FStar_Syntax_Print.tag_of_term im in
                       let uu____8756 =
                         let uu____8757 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____8757
                           (FStar_String.concat ", ") in
                       let uu____8760 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8752 uu____8753 uu____8754 uu____8755
                         uu____8756 uu____8760
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___130_8778 =
          match uu___130_8778 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____8807 = p in
          match uu____8807 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8865 = FStar_List.nth ps i in
              (match uu____8865 with
               | (pi,uu____8868) ->
                   let uu____8873 = FStar_List.nth xs i in
                   (match uu____8873 with
                    | (xi,uu____8880) ->
                        let rec gs k =
                          let uu____8889 = FStar_Syntax_Util.arrow_formals k in
                          match uu____8889 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8941)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8949 = new_uvar r xs k_a in
                                    (match uu____8949 with
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
                                         let uu____8968 = aux subst2 tl1 in
                                         (match uu____8968 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8983 =
                                                let uu____8985 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8985 :: gi_xs' in
                                              let uu____8986 =
                                                let uu____8988 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8988 :: gi_ps' in
                                              (uu____8983, uu____8986))) in
                              aux [] bs in
                        let uu____8991 =
                          let uu____8992 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8992 in
                        if uu____8991
                        then None
                        else
                          (let uu____8995 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8995 with
                           | (g_xs,uu____9002) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____9009 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r in
                                 let uu____9014 =
                                   let uu____9021 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_62  -> FStar_Util.Inl _0_62) in
                                   FStar_All.pipe_right uu____9021
                                     (fun _0_63  -> Some _0_63) in
                                 FStar_Syntax_Util.abs xs uu____9009
                                   uu____9014 in
                               let sub1 =
                                 let uu____9052 =
                                   let uu____9055 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let uu____9062 =
                                     let uu____9065 =
                                       FStar_List.map
                                         (fun uu____9071  ->
                                            match uu____9071 with
                                            | (uu____9076,uu____9077,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____9065 in
                                   mk_problem (p_scope orig) orig uu____9055
                                     (p_rel orig) uu____9062 None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____9052 in
                               ((let uu____9087 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____9087
                                 then
                                   let uu____9088 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____9089 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____9088 uu____9089
                                 else ());
                                (let wl2 =
                                   let uu____9092 =
                                     let uu____9094 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives.fst (p_guard sub1) in
                                     Some uu____9094 in
                                   solve_prob orig uu____9092
                                     [TERM (u, proj)] wl1 in
                                 let uu____9099 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_65  -> Some _0_65) uu____9099))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____9123 = lhs in
          match uu____9123 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____9146 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____9146 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____9172 =
                        let uu____9198 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____9198) in
                      Some uu____9172
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____9281 =
                           let uu____9285 =
                             let uu____9286 = FStar_Syntax_Subst.compress k in
                             uu____9286.FStar_Syntax_Syntax.n in
                           (uu____9285, args) in
                         match uu____9281 with
                         | (uu____9293,[]) ->
                             let uu____9295 =
                               let uu____9301 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____9301) in
                             Some uu____9295
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____9312,uu____9313) ->
                             let uu____9324 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9324 with
                              | (uv1,uv_args) ->
                                  let uu____9353 =
                                    let uu____9354 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9354.FStar_Syntax_Syntax.n in
                                  (match uu____9353 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9361) ->
                                       let uu____9374 =
                                         pat_vars env [] uv_args in
                                       (match uu____9374 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9388  ->
                                                      let uu____9389 =
                                                        let uu____9390 =
                                                          let uu____9391 =
                                                            let uu____9394 =
                                                              let uu____9395
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9395
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9394 in
                                                          fst uu____9391 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9390 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9389)) in
                                            let c1 =
                                              let uu____9401 =
                                                let uu____9402 =
                                                  let uu____9405 =
                                                    let uu____9406 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9406
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9405 in
                                                fst uu____9402 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9401 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9415 =
                                                let uu____9422 =
                                                  let uu____9428 =
                                                    let uu____9429 =
                                                      let uu____9432 =
                                                        let uu____9433 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9433
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9432 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9429 in
                                                  FStar_Util.Inl uu____9428 in
                                                Some uu____9422 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9415 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9453 -> None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9456,uu____9457)
                             ->
                             let uu____9469 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9469 with
                              | (uv1,uv_args) ->
                                  let uu____9498 =
                                    let uu____9499 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9499.FStar_Syntax_Syntax.n in
                                  (match uu____9498 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9506) ->
                                       let uu____9519 =
                                         pat_vars env [] uv_args in
                                       (match uu____9519 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9533  ->
                                                      let uu____9534 =
                                                        let uu____9535 =
                                                          let uu____9536 =
                                                            let uu____9539 =
                                                              let uu____9540
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9540
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9539 in
                                                          fst uu____9536 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9535 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9534)) in
                                            let c1 =
                                              let uu____9546 =
                                                let uu____9547 =
                                                  let uu____9550 =
                                                    let uu____9551 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9551
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9550 in
                                                fst uu____9547 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9546 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9560 =
                                                let uu____9567 =
                                                  let uu____9573 =
                                                    let uu____9574 =
                                                      let uu____9577 =
                                                        let uu____9578 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9578
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9577 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9574 in
                                                  FStar_Util.Inl uu____9573 in
                                                Some uu____9567 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9560 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9598 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9603)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____9635 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____9635
                                 (fun _0_66  -> Some _0_66)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9659 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____9659 with
                                  | (args1,rest) ->
                                      let uu____9677 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____9677 with
                                       | (xs2,c2) ->
                                           let uu____9685 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____9685
                                             (fun uu____9696  ->
                                                match uu____9696 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9718 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____9718 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____9766 =
                                        let uu____9769 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9769 in
                                      FStar_All.pipe_right uu____9766
                                        (fun _0_67  -> Some _0_67))
                         | uu____9777 ->
                             let uu____9781 =
                               let uu____9782 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____9783 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____9784 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9782 uu____9783 uu____9784 in
                             failwith uu____9781 in
                       let uu____9788 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____9788
                         (fun uu____9816  ->
                            match uu____9816 with
                            | (xs1,c1) ->
                                let uu____9844 =
                                  let uu____9867 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9867) in
                                Some uu____9844)) in
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
                     let uu____9939 = imitate orig env wl1 st in
                     match uu____9939 with
                     | Failed uu____9944 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9950 = project orig env wl1 i st in
                      match uu____9950 with
                      | None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some (Failed uu____9957) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____9971 = FStar_Syntax_Util.head_and_args t21 in
                match uu____9971 with
                | (hd1,uu____9982) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9997 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____10005 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____10006 -> true
                     | uu____10021 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____10024 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____10024
                         then true
                         else
                           ((let uu____10027 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____10027
                             then
                               let uu____10028 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____10028
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____10036 =
                    let uu____10039 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____10039 FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____10036 FStar_Syntax_Free.names in
                let uu____10070 = FStar_Util.set_is_empty fvs_hd in
                if uu____10070
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____10079 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____10079 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____10087 =
                            let uu____10088 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____10088 in
                          giveup_or_defer1 orig uu____10087
                        else
                          (let uu____10090 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____10090
                           then
                             let uu____10091 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____10091
                              then
                                let uu____10092 = subterms args_lhs in
                                imitate' orig env wl1 uu____10092
                              else
                                ((let uu____10096 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____10096
                                  then
                                    let uu____10097 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____10098 = names_to_string fvs1 in
                                    let uu____10099 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____10097 uu____10098 uu____10099
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____10104 ->
                                        let uu____10105 = sn_binders env vars in
                                        u_abs k_uv uu____10105 t21 in
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
                               (let uu____10114 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____10114
                                then
                                  ((let uu____10116 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____10116
                                    then
                                      let uu____10117 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____10118 = names_to_string fvs1 in
                                      let uu____10119 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____10117 uu____10118 uu____10119
                                    else ());
                                   (let uu____10121 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs)
                                      uu____10121 (- (Prims.parse_int "1"))))
                                else
                                  giveup env
                                    "free-variable check failed on a non-redex"
                                    orig)))
               | None  when patterns_only -> giveup env "not a pattern" orig
               | None  ->
                   if wl1.defer_ok
                   then solve env (defer "not a pattern" orig wl1)
                   else
                     (let uu____10135 =
                        let uu____10136 = FStar_Syntax_Free.names t1 in
                        check_head uu____10136 t2 in
                      if uu____10135
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____10140 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____10140
                          then
                            let uu____10141 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____10141
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____10144 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____10144 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____10189 =
               match uu____10189 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k in
                   let uu____10220 = FStar_Syntax_Util.arrow_formals k1 in
                   (match uu____10220 with
                    | (all_formals,uu____10231) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____10323  ->
                                        match uu____10323 with
                                        | (x,imp) ->
                                            let uu____10330 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____10330, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____10338 = FStar_Syntax_Util.type_u () in
                                match uu____10338 with
                                | (t1,uu____10342) ->
                                    let uu____10343 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    fst uu____10343 in
                              let uu____10346 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____10346 with
                               | (t',tm_u1) ->
                                   let uu____10353 = destruct_flex_t t' in
                                   (match uu____10353 with
                                    | (uu____10373,u1,k11,uu____10376) ->
                                        let sol =
                                          let uu____10404 =
                                            let uu____10409 =
                                              u_abs k1 all_formals t' in
                                            ((u, k1), uu____10409) in
                                          TERM uu____10404 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10469 = pat_var_opt env pat_args hd1 in
                              (match uu____10469 with
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
                                              (fun uu____10498  ->
                                                 match uu____10498 with
                                                 | (x,uu____10502) ->
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
                                      let uu____10508 =
                                        let uu____10509 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____10509 in
                                      if uu____10508
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10513 =
                                           FStar_Util.set_add (fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10513 formals1
                                           tl1)))
                          | uu____10519 -> failwith "Impossible" in
                        let uu____10530 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____10530 all_formals args) in
             let solve_both_pats wl1 uu____10570 uu____10571 r =
               match (uu____10570, uu____10571) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10685 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____10685
                   then
                     let uu____10686 = solve_prob orig None [] wl1 in
                     solve env uu____10686
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____10701 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____10701
                       then
                         let uu____10702 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____10703 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____10704 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____10705 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____10706 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10702 uu____10703 uu____10704 uu____10705
                           uu____10706
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____10754 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____10754 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10767 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____10767 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10799 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10799 in
                                  let uu____10802 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____10802 k3)
                           else
                             (let uu____10805 =
                                let uu____10806 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____10807 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____10808 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10806 uu____10807 uu____10808 in
                              failwith uu____10805) in
                       let uu____10809 =
                         let uu____10815 =
                           let uu____10823 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____10823 in
                         match uu____10815 with
                         | (bs,k1') ->
                             let uu____10841 =
                               let uu____10849 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____10849 in
                             (match uu____10841 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____10870 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_68  ->
                                         FStar_TypeChecker_Common.TProb _0_68)
                                      uu____10870 in
                                  let uu____10875 =
                                    let uu____10878 =
                                      let uu____10879 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____10879.FStar_Syntax_Syntax.n in
                                    let uu____10882 =
                                      let uu____10883 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____10883.FStar_Syntax_Syntax.n in
                                    (uu____10878, uu____10882) in
                                  (match uu____10875 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10891,uu____10892) ->
                                       (k1', [sub_prob])
                                   | (uu____10896,FStar_Syntax_Syntax.Tm_type
                                      uu____10897) -> (k2', [sub_prob])
                                   | uu____10901 ->
                                       let uu____10904 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____10904 with
                                        | (t,uu____10913) ->
                                            let uu____10914 = new_uvar r zs t in
                                            (match uu____10914 with
                                             | (k_zs,uu____10923) ->
                                                 let kprob =
                                                   let uu____10925 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_69  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_69) uu____10925 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____10809 with
                       | (k_u',sub_probs) ->
                           let uu____10939 =
                             let uu____10947 =
                               let uu____10948 = new_uvar r zs k_u' in
                               FStar_All.pipe_left FStar_Pervasives.fst
                                 uu____10948 in
                             let uu____10953 =
                               let uu____10956 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____10956 in
                             let uu____10959 =
                               let uu____10962 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____10962 in
                             (uu____10947, uu____10953, uu____10959) in
                           (match uu____10939 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____10981 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____10981 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____10993 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____10993
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____10997 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____10997 with
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
             let solve_one_pat uu____11029 uu____11030 =
               match (uu____11029, uu____11030) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____11094 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____11094
                     then
                       let uu____11095 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____11096 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____11095 uu____11096
                     else ());
                    (let uu____11098 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____11098
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____11105  ->
                              fun uu____11106  ->
                                match (uu____11105, uu____11106) with
                                | ((a,uu____11116),(t21,uu____11118)) ->
                                    let uu____11123 =
                                      let uu____11126 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____11126
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____11123
                                      (fun _0_70  ->
                                         FStar_TypeChecker_Common.TProb _0_70))
                           xs args2 in
                       let guard =
                         let uu____11130 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____11130 in
                       let wl1 = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____11140 = occurs_check env wl (u1, k1) t21 in
                        match uu____11140 with
                        | (occurs_ok,uu____11145) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____11150 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____11150
                            then
                              let sol =
                                let uu____11152 =
                                  let uu____11157 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____11157) in
                                TERM uu____11152 in
                              let wl1 = solve_prob orig None [sol] wl in
                              solve env wl1
                            else
                              (let uu____11162 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____11162
                               then
                                 let uu____11163 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____11163 with
                                 | (sol,(uu____11173,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____11183 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____11183
                                       then
                                         let uu____11184 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____11184
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____11189 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____11191 = lhs in
             match uu____11191 with
             | (t1,u1,k1,args1) ->
                 let uu____11196 = rhs in
                 (match uu____11196 with
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
                       | uu____11222 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____11228 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____11228 with
                              | (sol,uu____11235) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____11238 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____11238
                                    then
                                      let uu____11239 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____11239
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____11244 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____11246 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____11246
        then
          let uu____11247 = solve_prob orig None [] wl in
          solve env uu____11247
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____11251 = FStar_Util.physical_equality t1 t2 in
           if uu____11251
           then
             let uu____11252 = solve_prob orig None [] wl in
             solve env uu____11252
           else
             ((let uu____11255 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____11255
               then
                 let uu____11256 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____11256
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____11259,uu____11260) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____11261,FStar_Syntax_Syntax.Tm_bvar uu____11262) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___131_11302 =
                     match uu___131_11302 with
                     | [] -> c
                     | bs ->
                         let uu____11316 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c)) None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____11316 in
                   let uu____11326 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____11326 with
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
                                   let uu____11412 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____11412
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____11414 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_71  ->
                                      FStar_TypeChecker_Common.CProb _0_71)
                                   uu____11414))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___132_11491 =
                     match uu___132_11491 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l)) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____11526 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____11526 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11609 =
                                   let uu____11612 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____11613 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____11612
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11613 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_72  ->
                                      FStar_TypeChecker_Common.TProb _0_72)
                                   uu____11609))
               | (FStar_Syntax_Syntax.Tm_abs uu____11616,uu____11617) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11640 -> true
                     | uu____11655 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11683 =
                     let uu____11694 = maybe_eta t1 in
                     let uu____11699 = maybe_eta t2 in
                     (uu____11694, uu____11699) in
                   (match uu____11683 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___165_11730 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___165_11730.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___165_11730.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___165_11730.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___165_11730.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___165_11730.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___165_11730.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___165_11730.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___165_11730.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
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
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11771 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11771
                        then
                          let uu____11772 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11772 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11777 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11788,FStar_Syntax_Syntax.Tm_abs uu____11789) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11812 -> true
                     | uu____11827 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11855 =
                     let uu____11866 = maybe_eta t1 in
                     let uu____11871 = maybe_eta t2 in
                     (uu____11866, uu____11871) in
                   (match uu____11855 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___165_11902 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___165_11902.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___165_11902.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___165_11902.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___165_11902.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___165_11902.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___165_11902.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___165_11902.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___165_11902.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11921 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11921
                        then
                          let uu____11922 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11922 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11943 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11943
                        then
                          let uu____11944 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11944 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11949 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11960,FStar_Syntax_Syntax.Tm_refine uu____11961) ->
                   let uu____11970 = as_refinement env wl t1 in
                   (match uu____11970 with
                    | (x1,phi1) ->
                        let uu____11975 = as_refinement env wl t2 in
                        (match uu____11975 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11981 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_73  ->
                                    FStar_TypeChecker_Common.TProb _0_73)
                                 uu____11981 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____12014 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____12014
                                 (guard_on_element wl problem x11) in
                             let fallback uu____12018 =
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
                                 let uu____12024 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____12024 impl in
                               let wl1 = solve_prob orig (Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____12031 =
                                   let uu____12034 =
                                     let uu____12035 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____12035 :: (p_scope orig) in
                                   mk_problem uu____12034 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_74  ->
                                      FStar_TypeChecker_Common.TProb _0_74)
                                   uu____12031 in
                               let uu____12038 =
                                 solve env1
                                   (let uu___166_12039 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___166_12039.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___166_12039.smt_ok);
                                      tcenv = (uu___166_12039.tcenv)
                                    }) in
                               (match uu____12038 with
                                | Failed uu____12043 -> fallback ()
                                | Success uu____12046 ->
                                    let guard =
                                      let uu____12050 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives.fst in
                                      let uu____12053 =
                                        let uu____12054 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives.fst in
                                        FStar_All.pipe_right uu____12054
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____12050
                                        uu____12053 in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl2 =
                                      let uu___167_12061 = wl1 in
                                      {
                                        attempting =
                                          (uu___167_12061.attempting);
                                        wl_deferred =
                                          (uu___167_12061.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___167_12061.defer_ok);
                                        smt_ok = (uu___167_12061.smt_ok);
                                        tcenv = (uu___167_12061.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12063,FStar_Syntax_Syntax.Tm_uvar uu____12064) ->
                   let uu____12081 = destruct_flex_t t1 in
                   let uu____12082 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12081 uu____12082
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12083;
                     FStar_Syntax_Syntax.tk = uu____12084;
                     FStar_Syntax_Syntax.pos = uu____12085;
                     FStar_Syntax_Syntax.vars = uu____12086;_},uu____12087),FStar_Syntax_Syntax.Tm_uvar
                  uu____12088) ->
                   let uu____12119 = destruct_flex_t t1 in
                   let uu____12120 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12119 uu____12120
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12121,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12122;
                     FStar_Syntax_Syntax.tk = uu____12123;
                     FStar_Syntax_Syntax.pos = uu____12124;
                     FStar_Syntax_Syntax.vars = uu____12125;_},uu____12126))
                   ->
                   let uu____12157 = destruct_flex_t t1 in
                   let uu____12158 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12157 uu____12158
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12159;
                     FStar_Syntax_Syntax.tk = uu____12160;
                     FStar_Syntax_Syntax.pos = uu____12161;
                     FStar_Syntax_Syntax.vars = uu____12162;_},uu____12163),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12164;
                     FStar_Syntax_Syntax.tk = uu____12165;
                     FStar_Syntax_Syntax.pos = uu____12166;
                     FStar_Syntax_Syntax.vars = uu____12167;_},uu____12168))
                   ->
                   let uu____12213 = destruct_flex_t t1 in
                   let uu____12214 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12213 uu____12214
               | (FStar_Syntax_Syntax.Tm_uvar uu____12215,uu____12216) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12225 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____12225 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12229;
                     FStar_Syntax_Syntax.tk = uu____12230;
                     FStar_Syntax_Syntax.pos = uu____12231;
                     FStar_Syntax_Syntax.vars = uu____12232;_},uu____12233),uu____12234)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12257 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____12257 t2 wl
               | (uu____12261,FStar_Syntax_Syntax.Tm_uvar uu____12262) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____12271,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12272;
                     FStar_Syntax_Syntax.tk = uu____12273;
                     FStar_Syntax_Syntax.pos = uu____12274;
                     FStar_Syntax_Syntax.vars = uu____12275;_},uu____12276))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12299,FStar_Syntax_Syntax.Tm_type uu____12300) ->
                   solve_t' env
                     (let uu___168_12309 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_12309.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_12309.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_12309.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_12309.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_12309.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_12309.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_12309.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_12309.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_12309.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12310;
                     FStar_Syntax_Syntax.tk = uu____12311;
                     FStar_Syntax_Syntax.pos = uu____12312;
                     FStar_Syntax_Syntax.vars = uu____12313;_},uu____12314),FStar_Syntax_Syntax.Tm_type
                  uu____12315) ->
                   solve_t' env
                     (let uu___168_12338 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_12338.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_12338.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_12338.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_12338.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_12338.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_12338.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_12338.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_12338.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_12338.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12339,FStar_Syntax_Syntax.Tm_arrow uu____12340) ->
                   solve_t' env
                     (let uu___168_12356 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_12356.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_12356.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_12356.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_12356.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_12356.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_12356.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_12356.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_12356.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_12356.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12357;
                     FStar_Syntax_Syntax.tk = uu____12358;
                     FStar_Syntax_Syntax.pos = uu____12359;
                     FStar_Syntax_Syntax.vars = uu____12360;_},uu____12361),FStar_Syntax_Syntax.Tm_arrow
                  uu____12362) ->
                   solve_t' env
                     (let uu___168_12392 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_12392.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_12392.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_12392.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_12392.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_12392.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_12392.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_12392.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_12392.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_12392.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____12393,uu____12394) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12405 =
                        let uu____12406 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12406 in
                      if uu____12405
                      then
                        let uu____12407 =
                          FStar_All.pipe_left
                            (fun _0_75  ->
                               FStar_TypeChecker_Common.TProb _0_75)
                            (let uu___169_12410 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_12410.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_12410.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_12410.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_12410.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_12410.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___169_12410.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_12410.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_12410.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_12410.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12411 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12407 uu____12411 t2
                          wl
                      else
                        (let uu____12416 = base_and_refinement env wl t2 in
                         match uu____12416 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12446 =
                                    FStar_All.pipe_left
                                      (fun _0_76  ->
                                         FStar_TypeChecker_Common.TProb _0_76)
                                      (let uu___170_12449 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___170_12449.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___170_12449.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___170_12449.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___170_12449.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___170_12449.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___170_12449.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___170_12449.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___170_12449.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___170_12449.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12450 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12446
                                    uu____12450 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___171_12465 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___171_12465.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___171_12465.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12468 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_77  ->
                                         FStar_TypeChecker_Common.TProb _0_77)
                                      uu____12468 in
                                  let guard =
                                    let uu____12476 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12476
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12482;
                     FStar_Syntax_Syntax.tk = uu____12483;
                     FStar_Syntax_Syntax.pos = uu____12484;
                     FStar_Syntax_Syntax.vars = uu____12485;_},uu____12486),uu____12487)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12512 =
                        let uu____12513 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12513 in
                      if uu____12512
                      then
                        let uu____12514 =
                          FStar_All.pipe_left
                            (fun _0_78  ->
                               FStar_TypeChecker_Common.TProb _0_78)
                            (let uu___169_12517 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_12517.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_12517.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_12517.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_12517.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_12517.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___169_12517.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_12517.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_12517.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_12517.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12518 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12514 uu____12518 t2
                          wl
                      else
                        (let uu____12523 = base_and_refinement env wl t2 in
                         match uu____12523 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12553 =
                                    FStar_All.pipe_left
                                      (fun _0_79  ->
                                         FStar_TypeChecker_Common.TProb _0_79)
                                      (let uu___170_12556 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___170_12556.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___170_12556.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___170_12556.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___170_12556.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___170_12556.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___170_12556.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___170_12556.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___170_12556.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___170_12556.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12557 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12553
                                    uu____12557 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___171_12572 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___171_12572.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___171_12572.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12575 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_80  ->
                                         FStar_TypeChecker_Common.TProb _0_80)
                                      uu____12575 in
                                  let guard =
                                    let uu____12583 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12583
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12589,FStar_Syntax_Syntax.Tm_uvar uu____12590) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12600 = base_and_refinement env wl t1 in
                      match uu____12600 with
                      | (t_base,uu____12611) ->
                          solve_t env
                            (let uu___172_12626 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___172_12626.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___172_12626.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___172_12626.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___172_12626.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___172_12626.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___172_12626.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___172_12626.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___172_12626.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12629,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12630;
                     FStar_Syntax_Syntax.tk = uu____12631;
                     FStar_Syntax_Syntax.pos = uu____12632;
                     FStar_Syntax_Syntax.vars = uu____12633;_},uu____12634))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12658 = base_and_refinement env wl t1 in
                      match uu____12658 with
                      | (t_base,uu____12669) ->
                          solve_t env
                            (let uu___172_12684 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___172_12684.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___172_12684.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___172_12684.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___172_12684.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___172_12684.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___172_12684.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___172_12684.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___172_12684.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12687,uu____12688) ->
                   let t21 =
                     let uu____12696 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____12696 in
                   solve_t env
                     (let uu___173_12709 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_12709.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___173_12709.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___173_12709.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___173_12709.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_12709.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_12709.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_12709.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_12709.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_12709.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12710,FStar_Syntax_Syntax.Tm_refine uu____12711) ->
                   let t11 =
                     let uu____12719 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____12719 in
                   solve_t env
                     (let uu___174_12732 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_12732.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___174_12732.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___174_12732.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___174_12732.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_12732.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_12732.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_12732.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_12732.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_12732.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12735,uu____12736) ->
                   let head1 =
                     let uu____12755 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12755 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12786 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12786 FStar_Pervasives.fst in
                   let uu____12814 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12814
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12823 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12823
                      then
                        let guard =
                          let uu____12830 =
                            let uu____12831 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12831 = FStar_Syntax_Util.Equal in
                          if uu____12830
                          then None
                          else
                            (let uu____12834 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_81  -> Some _0_81)
                               uu____12834) in
                        let uu____12836 = solve_prob orig guard [] wl in
                        solve env uu____12836
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12839,uu____12840) ->
                   let head1 =
                     let uu____12848 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12848 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12879 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12879 FStar_Pervasives.fst in
                   let uu____12907 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12907
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12916 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12916
                      then
                        let guard =
                          let uu____12923 =
                            let uu____12924 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12924 = FStar_Syntax_Util.Equal in
                          if uu____12923
                          then None
                          else
                            (let uu____12927 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_82  -> Some _0_82)
                               uu____12927) in
                        let uu____12929 = solve_prob orig guard [] wl in
                        solve env uu____12929
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12932,uu____12933) ->
                   let head1 =
                     let uu____12937 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12937 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12968 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12968 FStar_Pervasives.fst in
                   let uu____12996 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12996
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13005 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13005
                      then
                        let guard =
                          let uu____13012 =
                            let uu____13013 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13013 = FStar_Syntax_Util.Equal in
                          if uu____13012
                          then None
                          else
                            (let uu____13016 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_83  -> Some _0_83)
                               uu____13016) in
                        let uu____13018 = solve_prob orig guard [] wl in
                        solve env uu____13018
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____13021,uu____13022) ->
                   let head1 =
                     let uu____13026 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13026 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13057 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13057 FStar_Pervasives.fst in
                   let uu____13085 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13085
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13094 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13094
                      then
                        let guard =
                          let uu____13101 =
                            let uu____13102 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13102 = FStar_Syntax_Util.Equal in
                          if uu____13101
                          then None
                          else
                            (let uu____13105 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_84  -> Some _0_84)
                               uu____13105) in
                        let uu____13107 = solve_prob orig guard [] wl in
                        solve env uu____13107
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____13110,uu____13111) ->
                   let head1 =
                     let uu____13115 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13115 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13146 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13146 FStar_Pervasives.fst in
                   let uu____13174 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13174
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13183 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13183
                      then
                        let guard =
                          let uu____13190 =
                            let uu____13191 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13191 = FStar_Syntax_Util.Equal in
                          if uu____13190
                          then None
                          else
                            (let uu____13194 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_85  -> Some _0_85)
                               uu____13194) in
                        let uu____13196 = solve_prob orig guard [] wl in
                        solve env uu____13196
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____13199,uu____13200) ->
                   let head1 =
                     let uu____13213 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13213 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13244 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13244 FStar_Pervasives.fst in
                   let uu____13272 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13272
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13281 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13281
                      then
                        let guard =
                          let uu____13288 =
                            let uu____13289 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13289 = FStar_Syntax_Util.Equal in
                          if uu____13288
                          then None
                          else
                            (let uu____13292 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_86  -> Some _0_86)
                               uu____13292) in
                        let uu____13294 = solve_prob orig guard [] wl in
                        solve env uu____13294
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13297,FStar_Syntax_Syntax.Tm_match uu____13298) ->
                   let head1 =
                     let uu____13317 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13317 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13348 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13348 FStar_Pervasives.fst in
                   let uu____13376 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13376
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13385 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13385
                      then
                        let guard =
                          let uu____13392 =
                            let uu____13393 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13393 = FStar_Syntax_Util.Equal in
                          if uu____13392
                          then None
                          else
                            (let uu____13396 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_87  -> Some _0_87)
                               uu____13396) in
                        let uu____13398 = solve_prob orig guard [] wl in
                        solve env uu____13398
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13401,FStar_Syntax_Syntax.Tm_uinst uu____13402) ->
                   let head1 =
                     let uu____13410 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13410 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13441 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13441 FStar_Pervasives.fst in
                   let uu____13469 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13469
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13478 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13478
                      then
                        let guard =
                          let uu____13485 =
                            let uu____13486 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13486 = FStar_Syntax_Util.Equal in
                          if uu____13485
                          then None
                          else
                            (let uu____13489 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_88  -> Some _0_88)
                               uu____13489) in
                        let uu____13491 = solve_prob orig guard [] wl in
                        solve env uu____13491
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13494,FStar_Syntax_Syntax.Tm_name uu____13495) ->
                   let head1 =
                     let uu____13499 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13499 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13530 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13530 FStar_Pervasives.fst in
                   let uu____13558 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13558
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13567 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13567
                      then
                        let guard =
                          let uu____13574 =
                            let uu____13575 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13575 = FStar_Syntax_Util.Equal in
                          if uu____13574
                          then None
                          else
                            (let uu____13578 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_89  -> Some _0_89)
                               uu____13578) in
                        let uu____13580 = solve_prob orig guard [] wl in
                        solve env uu____13580
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13583,FStar_Syntax_Syntax.Tm_constant uu____13584) ->
                   let head1 =
                     let uu____13588 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13588 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13619 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13619 FStar_Pervasives.fst in
                   let uu____13647 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13647
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13656 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13656
                      then
                        let guard =
                          let uu____13663 =
                            let uu____13664 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13664 = FStar_Syntax_Util.Equal in
                          if uu____13663
                          then None
                          else
                            (let uu____13667 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_90  -> Some _0_90)
                               uu____13667) in
                        let uu____13669 = solve_prob orig guard [] wl in
                        solve env uu____13669
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13672,FStar_Syntax_Syntax.Tm_fvar uu____13673) ->
                   let head1 =
                     let uu____13677 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13677 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13708 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13708 FStar_Pervasives.fst in
                   let uu____13736 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13736
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13745 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13745
                      then
                        let guard =
                          let uu____13752 =
                            let uu____13753 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13753 = FStar_Syntax_Util.Equal in
                          if uu____13752
                          then None
                          else
                            (let uu____13756 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_91  -> Some _0_91)
                               uu____13756) in
                        let uu____13758 = solve_prob orig guard [] wl in
                        solve env uu____13758
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13761,FStar_Syntax_Syntax.Tm_app uu____13762) ->
                   let head1 =
                     let uu____13775 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13775 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13806 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13806 FStar_Pervasives.fst in
                   let uu____13834 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13834
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13843 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13843
                      then
                        let guard =
                          let uu____13850 =
                            let uu____13851 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13851 = FStar_Syntax_Util.Equal in
                          if uu____13850
                          then None
                          else
                            (let uu____13854 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_92  -> Some _0_92)
                               uu____13854) in
                        let uu____13856 = solve_prob orig guard [] wl in
                        solve env uu____13856
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13860,uu____13861),uu____13862) ->
                   solve_t' env
                     (let uu___175_13891 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_13891.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_13891.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_13891.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_13891.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_13891.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_13891.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_13891.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_13891.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_13891.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13894,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13896,uu____13897)) ->
                   solve_t' env
                     (let uu___176_13926 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_13926.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___176_13926.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___176_13926.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___176_13926.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_13926.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_13926.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_13926.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_13926.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_13926.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13927,uu____13928) ->
                   let uu____13936 =
                     let uu____13937 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13938 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13937
                       uu____13938 in
                   failwith uu____13936
               | (FStar_Syntax_Syntax.Tm_meta uu____13939,uu____13940) ->
                   let uu____13945 =
                     let uu____13946 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13947 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13946
                       uu____13947 in
                   failwith uu____13945
               | (FStar_Syntax_Syntax.Tm_delayed uu____13948,uu____13949) ->
                   let uu____13970 =
                     let uu____13971 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13972 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13971
                       uu____13972 in
                   failwith uu____13970
               | (uu____13973,FStar_Syntax_Syntax.Tm_meta uu____13974) ->
                   let uu____13979 =
                     let uu____13980 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13981 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13980
                       uu____13981 in
                   failwith uu____13979
               | (uu____13982,FStar_Syntax_Syntax.Tm_delayed uu____13983) ->
                   let uu____14004 =
                     let uu____14005 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____14006 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____14005
                       uu____14006 in
                   failwith uu____14004
               | (uu____14007,FStar_Syntax_Syntax.Tm_let uu____14008) ->
                   let uu____14016 =
                     let uu____14017 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____14018 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____14017
                       uu____14018 in
                   failwith uu____14016
               | uu____14019 -> giveup env "head tag mismatch" orig)))
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
          (let uu____14051 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____14051
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____14059  ->
                  fun uu____14060  ->
                    match (uu____14059, uu____14060) with
                    | ((a1,uu____14070),(a2,uu____14072)) ->
                        let uu____14077 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_93  -> FStar_TypeChecker_Common.TProb _0_93)
                          uu____14077)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____14083 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p) FStar_Pervasives.fst)
                 sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____14083 in
           let wl1 = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____14103 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____14110)::[] -> wp1
              | uu____14123 ->
                  let uu____14129 =
                    let uu____14130 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____14130 in
                  failwith uu____14129 in
            let uu____14133 =
              let uu____14139 =
                let uu____14140 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____14140 in
              [uu____14139] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____14133;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____14141 = lift_c1 () in solve_eq uu____14141 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___133_14145  ->
                       match uu___133_14145 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____14146 -> false)) in
             let uu____14147 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____14171)::uu____14172,(wp2,uu____14174)::uu____14175)
                   -> (wp1, wp2)
               | uu____14216 ->
                   let uu____14229 =
                     let uu____14230 =
                       let uu____14233 =
                         let uu____14234 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____14235 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____14234 uu____14235 in
                       (uu____14233, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____14230 in
                   raise uu____14229 in
             match uu____14147 with
             | (wpc1,wpc2) ->
                 let uu____14252 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____14252
                 then
                   let uu____14255 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env uu____14255 wl
                 else
                   (let uu____14259 =
                      let uu____14263 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____14263 in
                    match uu____14259 with
                    | (c2_decl,qualifiers) ->
                        let uu____14275 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____14275
                        then
                          let c1_repr =
                            let uu____14278 =
                              let uu____14279 =
                                let uu____14280 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____14280 in
                              let uu____14281 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14279 uu____14281 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14278 in
                          let c2_repr =
                            let uu____14283 =
                              let uu____14284 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____14285 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14284 uu____14285 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14283 in
                          let prob =
                            let uu____14287 =
                              let uu____14290 =
                                let uu____14291 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____14292 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____14291
                                  uu____14292 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____14290 in
                            FStar_TypeChecker_Common.TProb uu____14287 in
                          let wl1 =
                            let uu____14294 =
                              let uu____14296 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives.fst in
                              Some uu____14296 in
                            solve_prob orig uu____14294 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____14303 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____14303
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____14305 =
                                     let uu____14308 =
                                       let uu____14309 =
                                         let uu____14319 =
                                           let uu____14320 =
                                             let uu____14321 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____14321] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____14320 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____14322 =
                                           let uu____14324 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____14325 =
                                             let uu____14327 =
                                               let uu____14328 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____14328 in
                                             [uu____14327] in
                                           uu____14324 :: uu____14325 in
                                         (uu____14319, uu____14322) in
                                       FStar_Syntax_Syntax.Tm_app uu____14309 in
                                     FStar_Syntax_Syntax.mk uu____14308 in
                                   uu____14305
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____14339 =
                                    let uu____14342 =
                                      let uu____14343 =
                                        let uu____14353 =
                                          let uu____14354 =
                                            let uu____14355 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____14355] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____14354 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____14356 =
                                          let uu____14358 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____14359 =
                                            let uu____14361 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____14362 =
                                              let uu____14364 =
                                                let uu____14365 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14365 in
                                              [uu____14364] in
                                            uu____14361 :: uu____14362 in
                                          uu____14358 :: uu____14359 in
                                        (uu____14353, uu____14356) in
                                      FStar_Syntax_Syntax.Tm_app uu____14343 in
                                    FStar_Syntax_Syntax.mk uu____14342 in
                                  uu____14339
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____14376 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_94  ->
                                  FStar_TypeChecker_Common.TProb _0_94)
                               uu____14376 in
                           let wl1 =
                             let uu____14382 =
                               let uu____14384 =
                                 let uu____14387 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____14387 g in
                               FStar_All.pipe_left (fun _0_95  -> Some _0_95)
                                 uu____14384 in
                             solve_prob orig uu____14382 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____14397 = FStar_Util.physical_equality c1 c2 in
        if uu____14397
        then
          let uu____14398 = solve_prob orig None [] wl in
          solve env uu____14398
        else
          ((let uu____14401 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____14401
            then
              let uu____14402 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____14403 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14402
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14403
            else ());
           (let uu____14405 =
              let uu____14408 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____14409 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____14408, uu____14409) in
            match uu____14405 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14413),FStar_Syntax_Syntax.Total
                    (t2,uu____14415)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14428 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14428 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14431,FStar_Syntax_Syntax.Total uu____14432) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14444),FStar_Syntax_Syntax.Total
                    (t2,uu____14446)) ->
                     let uu____14459 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14459 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14463),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14465)) ->
                     let uu____14478 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14478 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14482),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14484)) ->
                     let uu____14497 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14497 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14500,FStar_Syntax_Syntax.Comp uu____14501) ->
                     let uu____14507 =
                       let uu___177_14510 = problem in
                       let uu____14513 =
                         let uu____14514 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14514 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14510.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14513;
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14510.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___177_14510.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___177_14510.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14510.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14510.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14510.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14510.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14510.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14507 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14515,FStar_Syntax_Syntax.Comp uu____14516) ->
                     let uu____14522 =
                       let uu___177_14525 = problem in
                       let uu____14528 =
                         let uu____14529 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14529 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14525.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14528;
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14525.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___177_14525.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___177_14525.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14525.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14525.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14525.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14525.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14525.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14522 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14530,FStar_Syntax_Syntax.GTotal uu____14531) ->
                     let uu____14537 =
                       let uu___178_14540 = problem in
                       let uu____14543 =
                         let uu____14544 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14544 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14540.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___178_14540.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14540.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14543;
                         FStar_TypeChecker_Common.element =
                           (uu___178_14540.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14540.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14540.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14540.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14540.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14540.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14537 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14545,FStar_Syntax_Syntax.Total uu____14546) ->
                     let uu____14552 =
                       let uu___178_14555 = problem in
                       let uu____14558 =
                         let uu____14559 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14559 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14555.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___178_14555.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14555.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14558;
                         FStar_TypeChecker_Common.element =
                           (uu___178_14555.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14555.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14555.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14555.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14555.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14555.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14552 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14560,FStar_Syntax_Syntax.Comp uu____14561) ->
                     let uu____14562 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____14562
                     then
                       let uu____14563 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type" in
                       solve_t env uu____14563 wl
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
                           (let uu____14573 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____14573
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14575 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____14575 with
                            | None  ->
                                let uu____14577 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14578 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____14578) in
                                if uu____14577
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
                                  (let uu____14581 =
                                     let uu____14582 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____14583 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14582 uu____14583 in
                                   giveup env uu____14581 orig)
                            | Some edge -> solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14589 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14605  ->
              match uu____14605 with
              | (uu____14612,uu____14613,u,uu____14615,uu____14616,uu____14617)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____14589 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14636 =
        FStar_All.pipe_right (fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____14636 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____14646 =
        FStar_All.pipe_right (snd ineqs)
          (FStar_List.map
             (fun uu____14658  ->
                match uu____14658 with
                | (u1,u2) ->
                    let uu____14663 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____14664 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____14663 uu____14664)) in
      FStar_All.pipe_right uu____14646 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14678,[])) -> "{}"
      | uu____14691 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14701 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____14701
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____14704 =
              FStar_List.map
                (fun uu____14708  ->
                   match uu____14708 with
                   | (uu____14711,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____14704 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____14715 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14715 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14760 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____14760
    then
      let uu____14761 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____14762 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14761
        (rel_to_string rel) uu____14762
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
            let uu____14786 =
              let uu____14788 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_96  -> Some _0_96) uu____14788 in
            FStar_Syntax_Syntax.new_bv uu____14786 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____14794 =
              let uu____14796 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_97  -> Some _0_97) uu____14796 in
            let uu____14798 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____14794 uu____14798 in
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
          let uu____14824 = FStar_Options.eager_inference () in
          if uu____14824
          then
            let uu___179_14825 = probs in
            {
              attempting = (uu___179_14825.attempting);
              wl_deferred = (uu___179_14825.wl_deferred);
              ctr = (uu___179_14825.ctr);
              defer_ok = false;
              smt_ok = (uu___179_14825.smt_ok);
              tcenv = (uu___179_14825.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Syntax_Unionfind.rollback tx;
             (let uu____14836 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____14836
              then
                let uu____14837 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____14837
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
          ((let uu____14849 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____14849
            then
              let uu____14850 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14850
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f in
            (let uu____14854 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____14854
             then
               let uu____14855 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14855
             else ());
            (let f2 =
               let uu____14858 =
                 let uu____14859 = FStar_Syntax_Util.unmeta f1 in
                 uu____14859.FStar_Syntax_Syntax.n in
               match uu____14858 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14863 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___180_14864 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___180_14864.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___180_14864.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___180_14864.FStar_TypeChecker_Env.implicits)
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
            let uu____14882 =
              let uu____14883 =
                let uu____14884 =
                  let uu____14885 =
                    FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____14885
                    (fun _0_98  -> FStar_TypeChecker_Common.NonTrivial _0_98) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14884;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____14883 in
            FStar_All.pipe_left (fun _0_99  -> Some _0_99) uu____14882
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____14922 =
        let uu____14923 =
          let uu____14924 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
          FStar_All.pipe_right uu____14924
            (fun _0_100  -> FStar_TypeChecker_Common.NonTrivial _0_100) in
        {
          FStar_TypeChecker_Env.guard_f = uu____14923;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      Some uu____14922
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
          (let uu____14954 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14954
           then
             let uu____14955 = FStar_Syntax_Print.term_to_string t1 in
             let uu____14956 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14955
               uu____14956
           else ());
          (let prob =
             let uu____14959 =
               let uu____14962 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____14962 in
             FStar_All.pipe_left
               (fun _0_101  -> FStar_TypeChecker_Common.TProb _0_101)
               uu____14959 in
           let g =
             let uu____14967 =
               let uu____14969 = singleton' env prob smt_ok in
               solve_and_commit env uu____14969 (fun uu____14970  -> None) in
             FStar_All.pipe_left (with_guard env prob) uu____14967 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14987 = try_teq true env t1 t2 in
        match uu____14987 with
        | None  ->
            let uu____14989 =
              let uu____14990 =
                let uu____14993 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                let uu____14994 = FStar_TypeChecker_Env.get_range env in
                (uu____14993, uu____14994) in
              FStar_Errors.Error uu____14990 in
            raise uu____14989
        | Some g ->
            ((let uu____14997 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____14997
              then
                let uu____14998 = FStar_Syntax_Print.term_to_string t1 in
                let uu____14999 = FStar_Syntax_Print.term_to_string t2 in
                let uu____15000 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14998
                  uu____14999 uu____15000
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
          (let uu____15020 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____15020
           then
             let uu____15021 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____15022 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____15021
               uu____15022
           else ());
          (let uu____15024 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____15024 with
           | (prob,x) ->
               let g =
                 let uu____15032 =
                   let uu____15034 = singleton' env prob smt_ok in
                   solve_and_commit env uu____15034
                     (fun uu____15035  -> None) in
                 FStar_All.pipe_left (with_guard env prob) uu____15032 in
               ((let uu____15041 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____15041
                 then
                   let uu____15042 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____15043 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____15044 =
                     let uu____15045 = FStar_Util.must g in
                     guard_to_string env uu____15045 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____15042 uu____15043 uu____15044
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
          let uu____15076 = FStar_TypeChecker_Env.get_range env in
          let uu____15077 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.err uu____15076 uu____15077
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____15092 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____15092
         then
           let uu____15093 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____15094 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____15093
             uu____15094
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____15099 =
             let uu____15102 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None uu____15102 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_102  -> FStar_TypeChecker_Common.CProb _0_102)
             uu____15099 in
         let uu____15105 =
           let uu____15107 = singleton env prob in
           solve_and_commit env uu____15107 (fun uu____15108  -> None) in
         FStar_All.pipe_left (with_guard env prob) uu____15105)
let solve_universe_inequalities':
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____15130  ->
        match uu____15130 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____15155 =
                 let uu____15156 =
                   let uu____15159 =
                     let uu____15160 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____15161 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____15160 uu____15161 in
                   let uu____15162 = FStar_TypeChecker_Env.get_range env in
                   (uu____15159, uu____15162) in
                 FStar_Errors.Error uu____15156 in
               raise uu____15155) in
            let equiv1 v1 v' =
              let uu____15170 =
                let uu____15173 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____15174 = FStar_Syntax_Subst.compress_univ v' in
                (uu____15173, uu____15174) in
              match uu____15170 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____15181 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____15195 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____15195 with
                      | FStar_Syntax_Syntax.U_unif uu____15199 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____15210  ->
                                    match uu____15210 with
                                    | (u,v') ->
                                        let uu____15216 = equiv1 v1 v' in
                                        if uu____15216
                                        then
                                          let uu____15218 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____15218 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____15228 -> [])) in
            let uu____15231 =
              let wl =
                let uu___181_15234 = empty_worklist env in
                {
                  attempting = (uu___181_15234.attempting);
                  wl_deferred = (uu___181_15234.wl_deferred);
                  ctr = (uu___181_15234.ctr);
                  defer_ok = false;
                  smt_ok = (uu___181_15234.smt_ok);
                  tcenv = (uu___181_15234.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____15241  ->
                      match uu____15241 with
                      | (lb,v1) ->
                          let uu____15246 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____15246 with
                           | USolved wl1 -> ()
                           | uu____15248 -> fail lb v1))) in
            let rec check_ineq uu____15254 =
              match uu____15254 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____15261) -> true
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
                      uu____15272,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____15274,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____15279) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____15283,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____15288 -> false) in
            let uu____15291 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____15297  ->
                      match uu____15297 with
                      | (u,v1) ->
                          let uu____15302 = check_ineq (u, v1) in
                          if uu____15302
                          then true
                          else
                            ((let uu____15305 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____15305
                              then
                                let uu____15306 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____15307 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____15306
                                  uu____15307
                              else ());
                             false))) in
            if uu____15291
            then ()
            else
              ((let uu____15311 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____15311
                then
                  ((let uu____15313 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____15313);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____15319 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____15319))
                else ());
               (let uu____15325 =
                  let uu____15326 =
                    let uu____15329 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____15329) in
                  FStar_Errors.Error uu____15326 in
                raise uu____15325))
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
      let fail uu____15366 =
        match uu____15366 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____15376 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____15376
       then
         let uu____15377 = wl_to_string wl in
         let uu____15378 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____15377 uu____15378
       else ());
      (let g1 =
         let uu____15393 = solve_and_commit env wl fail in
         match uu____15393 with
         | Some [] ->
             let uu___182_15400 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___182_15400.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___182_15400.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___182_15400.FStar_TypeChecker_Env.implicits)
             }
         | uu____15403 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___183_15406 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___183_15406.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___183_15406.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___183_15406.FStar_TypeChecker_Env.implicits)
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
            let uu___184_15436 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___184_15436.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___184_15436.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___184_15436.FStar_TypeChecker_Env.implicits)
            } in
          let uu____15437 =
            let uu____15438 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____15438 in
          if uu____15437
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15444 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____15444
                   then
                     let uu____15445 = FStar_TypeChecker_Env.get_range env in
                     let uu____15446 =
                       let uu____15447 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15447 in
                     FStar_Errors.diag uu____15445 uu____15446
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   let uu____15450 = check_trivial vc1 in
                   match uu____15450 with
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
                         ((let uu____15463 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15463
                           then
                             let uu____15464 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____15465 =
                               let uu____15466 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15466 in
                             FStar_Errors.diag uu____15464 uu____15465
                           else ());
                          (let vcs =
                             let uu____15473 = FStar_Options.use_tactics () in
                             if uu____15473
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
                                (fun uu____15497  ->
                                   match uu____15497 with
                                   | (env1,goal,opts) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify;
                                           FStar_TypeChecker_Normalize.Primops]
                                           env1 goal in
                                       let uu____15505 = check_trivial goal1 in
                                       (match uu____15505 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____15507 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____15507
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
                                             (let uu____15514 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____15514
                                              then
                                                let uu____15515 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____15516 =
                                                  let uu____15517 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____15518 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____15517 uu____15518 in
                                                FStar_Errors.diag uu____15515
                                                  uu____15516
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
      let uu____15530 = discharge_guard' None env g false in
      match uu____15530 with
      | Some g1 -> g1
      | None  ->
          let uu____15535 =
            let uu____15536 =
              let uu____15539 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____15539) in
            FStar_Errors.Error uu____15536 in
          raise uu____15535
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15548 = discharge_guard' None env g true in
      match uu____15548 with
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
  fun g  -> resolve_implicits' false g
let resolve_implicits_lax:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  -> resolve_implicits' true g
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____15735 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____15735 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15742 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15742
      | (reason,uu____15744,uu____15745,e,t,r)::uu____15749 ->
          let uu____15763 =
            let uu____15764 = FStar_Syntax_Print.term_to_string t in
            let uu____15765 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2
              "Failed to resolve implicit argument of type '%s' introduced in %s"
              uu____15764 uu____15765 in
          FStar_Errors.err r uu____15763
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___189_15774 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___189_15774.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___189_15774.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___189_15774.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15795 = try_teq false env t1 t2 in
        match uu____15795 with
        | None  -> false
        | Some g ->
            let uu____15798 = discharge_guard' None env g false in
            (match uu____15798 with
             | Some uu____15802 -> true
             | None  -> false)