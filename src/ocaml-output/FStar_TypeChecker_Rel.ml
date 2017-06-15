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
        FStar_TypeChecker_Env.univ_ineqs = uu____20;
        FStar_TypeChecker_Env.implicits = uu____21;_} -> true
    | uu____35 -> false
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
            FStar_TypeChecker_Env.deferred = uu____56;
            FStar_TypeChecker_Env.univ_ineqs = uu____57;
            FStar_TypeChecker_Env.implicits = uu____58;_}
          -> g
      | Some g1 ->
          let f =
            match g1.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.NonTrivial f -> f
            | uu____73 -> failwith "impossible" in
          let uu____74 =
            let uu___134_75 = g1 in
            let uu____76 =
              let uu____77 =
                let uu____78 =
                  let uu____79 = FStar_Syntax_Syntax.mk_binder x in
                  [uu____79] in
                let uu____80 =
                  let uu____87 =
                    let uu____93 =
                      let uu____94 =
                        FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                      FStar_All.pipe_right uu____94
                        FStar_Syntax_Util.lcomp_of_comp in
                    FStar_All.pipe_right uu____93
                      (fun _0_39  -> FStar_Util.Inl _0_39) in
                  Some uu____87 in
                FStar_Syntax_Util.abs uu____78 f uu____80 in
              FStar_All.pipe_left
                (fun _0_40  -> FStar_TypeChecker_Common.NonTrivial _0_40)
                uu____77 in
            {
              FStar_TypeChecker_Env.guard_f = uu____76;
              FStar_TypeChecker_Env.deferred =
                (uu___134_75.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___134_75.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___134_75.FStar_TypeChecker_Env.implicits)
            } in
          Some uu____74
let apply_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___135_115 = g in
          let uu____116 =
            let uu____117 =
              let uu____118 =
                let uu____121 =
                  let uu____122 =
                    let uu____132 =
                      let uu____134 = FStar_Syntax_Syntax.as_arg e in
                      [uu____134] in
                    (f, uu____132) in
                  FStar_Syntax_Syntax.Tm_app uu____122 in
                FStar_Syntax_Syntax.mk uu____121 in
              uu____118
                (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun _0_41  -> FStar_TypeChecker_Common.NonTrivial _0_41)
              uu____117 in
          {
            FStar_TypeChecker_Env.guard_f = uu____116;
            FStar_TypeChecker_Env.deferred =
              (uu___135_115.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___135_115.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___135_115.FStar_TypeChecker_Env.implicits)
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
          let uu___136_156 = g in
          let uu____157 =
            let uu____158 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____158 in
          {
            FStar_TypeChecker_Env.guard_f = uu____157;
            FStar_TypeChecker_Env.deferred =
              (uu___136_156.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___136_156.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___136_156.FStar_TypeChecker_Env.implicits)
          }
let trivial: FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____162 -> failwith "impossible"
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
          let uu____173 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____173
let check_trivial:
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula =
  fun t  ->
    let uu____177 =
      let uu____178 = FStar_Syntax_Util.unmeta t in
      uu____178.FStar_Syntax_Syntax.n in
    match uu____177 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____182 -> FStar_TypeChecker_Common.NonTrivial t
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
        let uu____213 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
        {
          FStar_TypeChecker_Env.guard_f = uu____213;
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
                       let uu____258 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____258
                       then f1
                       else FStar_Syntax_Util.mk_forall u (fst b) f1) us bs f in
            let uu___137_260 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___137_260.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___137_260.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___137_260.FStar_TypeChecker_Env.implicits)
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
            let uu___138_287 = g in
            let uu____288 =
              let uu____289 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____289 in
            {
              FStar_TypeChecker_Env.guard_f = uu____288;
              FStar_TypeChecker_Env.deferred =
                (uu___138_287.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___138_287.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___138_287.FStar_TypeChecker_Env.implicits)
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
        | uu____317 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____332 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____332 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                None r in
            let uu____344 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                (Some (k.FStar_Syntax_Syntax.n)) r in
            (uu____344, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____373 = FStar_Syntax_Util.type_u () in
        match uu____373 with
        | (t_type,u) ->
            let uu____378 =
              let uu____381 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____381 t_type in
            (match uu____378 with
             | (tt,uu____383) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of ((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
  FStar_Syntax_Syntax.term)
  | UNIV of (FStar_Syntax_Syntax.universe_uvar* FStar_Syntax_Syntax.universe)
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____406 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
      FStar_Syntax_Syntax.term)
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____432 -> false
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
    match projectee with | Success _0 -> true | uu____574 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____588 -> false
let __proj__Failed__item___0:
  solution -> (FStar_TypeChecker_Common.prob* Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0
type variance =
  | COVARIANT
  | CONTRAVARIANT
  | INVARIANT
let uu___is_COVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____605 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____609 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____613 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___106_630  ->
    match uu___106_630 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____643 =
    let uu____644 = FStar_Syntax_Subst.compress t in
    uu____644.FStar_Syntax_Syntax.n in
  match uu____643 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____661 = FStar_Syntax_Print.uvar_to_string u in
      let uu____662 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____661 uu____662
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____665;
         FStar_Syntax_Syntax.pos = uu____666;
         FStar_Syntax_Syntax.vars = uu____667;_},args)
      ->
      let uu____695 = FStar_Syntax_Print.uvar_to_string u in
      let uu____696 = FStar_Syntax_Print.term_to_string ty in
      let uu____697 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" uu____695 uu____696 uu____697
  | uu____698 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___107_704  ->
      match uu___107_704 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____708 =
            let uu____710 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____711 =
              let uu____713 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____714 =
                let uu____716 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____717 =
                  let uu____719 =
                    let uu____721 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____722 =
                      let uu____724 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____725 =
                        let uu____727 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (fst p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____728 =
                          let uu____730 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____730] in
                        uu____727 :: uu____728 in
                      uu____724 :: uu____725 in
                    uu____721 :: uu____722 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____719 in
                uu____716 :: uu____717 in
              uu____713 :: uu____714 in
            uu____710 :: uu____711 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____708
      | FStar_TypeChecker_Common.CProb p ->
          let uu____735 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____736 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____735
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____736
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___108_742  ->
      match uu___108_742 with
      | UNIV (u,t) ->
          let x =
            let uu____746 = FStar_Options.hide_uvar_nums () in
            if uu____746
            then "?"
            else
              (let uu____748 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____748 FStar_Util.string_of_int) in
          let uu____749 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____749
      | TERM ((u,uu____751),t) ->
          let x =
            let uu____756 = FStar_Options.hide_uvar_nums () in
            if uu____756
            then "?"
            else
              (let uu____758 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____758 FStar_Util.string_of_int) in
          let uu____759 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____759
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____768 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____768 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____776 =
      let uu____778 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____778
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____776 (FStar_String.concat ", ")
let args_to_string args =
  let uu____796 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____804  ->
            match uu____804 with
            | (x,uu____808) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right uu____796 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____813 =
      let uu____814 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____814 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____813;
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
        let uu___139_827 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___139_827.wl_deferred);
          ctr = (uu___139_827.ctr);
          defer_ok = (uu___139_827.defer_ok);
          smt_ok;
          tcenv = (uu___139_827.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___140_852 = empty_worklist env in
  let uu____853 = FStar_List.map FStar_Pervasives.snd g in
  {
    attempting = uu____853;
    wl_deferred = (uu___140_852.wl_deferred);
    ctr = (uu___140_852.ctr);
    defer_ok = false;
    smt_ok = (uu___140_852.smt_ok);
    tcenv = (uu___140_852.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___141_865 = wl in
        {
          attempting = (uu___141_865.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___141_865.ctr);
          defer_ok = (uu___141_865.defer_ok);
          smt_ok = (uu___141_865.smt_ok);
          tcenv = (uu___141_865.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___142_877 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___142_877.wl_deferred);
        ctr = (uu___142_877.ctr);
        defer_ok = (uu___142_877.defer_ok);
        smt_ok = (uu___142_877.smt_ok);
        tcenv = (uu___142_877.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____888 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____888
         then
           let uu____889 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____889
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___109_893  ->
    match uu___109_893 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___143_909 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___143_909.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___143_909.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___143_909.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___143_909.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___143_909.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___143_909.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___143_909.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___110_930  ->
    match uu___110_930 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_43  -> FStar_TypeChecker_Common.CProb _0_43)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___111_946  ->
      match uu___111_946 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___112_949  ->
    match uu___112_949 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___113_958  ->
    match uu___113_958 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___114_968  ->
    match uu___114_968 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___115_978  ->
    match uu___115_978 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun uu___116_989  ->
    match uu___116_989 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___117_1000  ->
    match uu___117_1000 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___118_1009  ->
    match uu___118_1009 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.TProb _0_44) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_45  -> FStar_TypeChecker_Common.CProb _0_45) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____1023 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1023 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1038  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1088 = next_pid () in
  let uu____1089 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1088;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1089;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1136 = next_pid () in
  let uu____1137 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1136;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1137;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1178 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1178;
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
        let uu____1230 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1230
        then
          let uu____1231 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1232 = prob_to_string env d in
          let uu____1233 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1231 uu____1232 uu____1233 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1238 -> failwith "impossible" in
           let uu____1239 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1247 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1248 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1247, uu____1248)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1252 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1253 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1252, uu____1253) in
           match uu____1239 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___119_1262  ->
            match uu___119_1262 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1268 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1270),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___120_1283  ->
           match uu___120_1283 with
           | UNIV uu____1285 -> None
           | TERM ((u,uu____1289),t) ->
               let uu____1293 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1293 then Some t else None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___121_1305  ->
           match uu___121_1305 with
           | UNIV (u',t) ->
               let uu____1309 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1309 then Some t else None
           | uu____1312 -> None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1319 =
        let uu____1320 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1320 in
      FStar_Syntax_Subst.compress uu____1319
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1327 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1327
let norm_arg env t = let uu____1346 = sn env (fst t) in (uu____1346, (snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1363  ->
              match uu____1363 with
              | (x,imp) ->
                  let uu____1370 =
                    let uu___144_1371 = x in
                    let uu____1372 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___144_1371.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___144_1371.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1372
                    } in
                  (uu____1370, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1387 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1387
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1390 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1390
        | uu____1392 -> u2 in
      let uu____1393 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1393
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1500 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____1500 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1512;
               FStar_Syntax_Syntax.pos = uu____1513;
               FStar_Syntax_Syntax.vars = uu____1514;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1535 =
                 let uu____1536 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1537 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1536
                   uu____1537 in
               failwith uu____1535)
    | FStar_Syntax_Syntax.Tm_uinst uu____1547 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1574 =
             let uu____1575 = FStar_Syntax_Subst.compress t1' in
             uu____1575.FStar_Syntax_Syntax.n in
           match uu____1574 with
           | FStar_Syntax_Syntax.Tm_refine uu____1587 -> aux true t1'
           | uu____1592 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1604 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1627 =
             let uu____1628 = FStar_Syntax_Subst.compress t1' in
             uu____1628.FStar_Syntax_Syntax.n in
           match uu____1627 with
           | FStar_Syntax_Syntax.Tm_refine uu____1640 -> aux true t1'
           | uu____1645 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_app uu____1657 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1689 =
             let uu____1690 = FStar_Syntax_Subst.compress t1' in
             uu____1690.FStar_Syntax_Syntax.n in
           match uu____1689 with
           | FStar_Syntax_Syntax.Tm_refine uu____1702 -> aux true t1'
           | uu____1707 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_type uu____1719 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_constant uu____1731 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_name uu____1743 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1755 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1767 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_abs uu____1786 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1812 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_let uu____1832 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_match uu____1851 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_meta uu____1878 ->
        let uu____1883 =
          let uu____1884 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1885 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1884
            uu____1885 in
        failwith uu____1883
    | FStar_Syntax_Syntax.Tm_ascribed uu____1895 ->
        let uu____1913 =
          let uu____1914 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1915 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1914
            uu____1915 in
        failwith uu____1913
    | FStar_Syntax_Syntax.Tm_delayed uu____1925 ->
        let uu____1946 =
          let uu____1947 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1948 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1947
            uu____1948 in
        failwith uu____1946
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1958 =
          let uu____1959 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1960 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1959
            uu____1960 in
        failwith uu____1958 in
  let uu____1970 = whnf env t1 in aux false uu____1970
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1979 =
        let uu____1989 = empty_worklist env in
        base_and_refinement env uu____1989 t in
      FStar_All.pipe_right uu____1979 FStar_Pervasives.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____2013 = FStar_Syntax_Syntax.null_bv t in
    (uu____2013, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____2033 = base_and_refinement env wl t in
  match uu____2033 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
let force_refinement uu____2092 =
  match uu____2092 with
  | (t_base,refopt) ->
      let uu____2106 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base in
      (match uu____2106 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___122_2130  ->
      match uu___122_2130 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2134 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2135 =
            let uu____2136 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____2136 in
          let uu____2137 =
            let uu____2138 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____2138 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2134 uu____2135
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2137
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2142 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2143 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____2144 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2142 uu____2143
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2144
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2148 =
      let uu____2150 =
        let uu____2152 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2162  ->
                  match uu____2162 with | (uu____2166,uu____2167,x) -> x)) in
        FStar_List.append wl.attempting uu____2152 in
      FStar_List.map (wl_prob_to_string wl) uu____2150 in
    FStar_All.pipe_right uu____2148 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2185 =
          let uu____2195 =
            let uu____2196 = FStar_Syntax_Subst.compress k in
            uu____2196.FStar_Syntax_Syntax.n in
          match uu____2195 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2241 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2241)
              else
                (let uu____2255 = FStar_Syntax_Util.abs_formals t in
                 match uu____2255 with
                 | (ys',t1,uu____2276) ->
                     let uu____2289 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2289))
          | uu____2310 ->
              let uu____2311 =
                let uu____2317 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____2317) in
              ((ys, t), uu____2311) in
        match uu____2185 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2376 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2376 c in
               let uu____2378 =
                 let uu____2385 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_46  -> FStar_Util.Inl _0_46) in
                 FStar_All.pipe_right uu____2385 (fun _0_47  -> Some _0_47) in
               FStar_Syntax_Util.abs ys1 t1 uu____2378)
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
            let uu____2436 = p_guard prob in
            match uu____2436 with
            | (uu____2439,uv) ->
                ((let uu____2442 =
                    let uu____2443 = FStar_Syntax_Subst.compress uv in
                    uu____2443.FStar_Syntax_Syntax.n in
                  match uu____2442 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2463 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2463
                        then
                          let uu____2464 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2465 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2466 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2464
                            uu____2465 uu____2466
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2468 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___145_2471 = wl in
                  {
                    attempting = (uu___145_2471.attempting);
                    wl_deferred = (uu___145_2471.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___145_2471.defer_ok);
                    smt_ok = (uu___145_2471.smt_ok);
                    tcenv = (uu___145_2471.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2484 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2484
         then
           let uu____2485 = FStar_Util.string_of_int pid in
           let uu____2486 =
             let uu____2487 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2487 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2485 uu____2486
         else ());
        commit sol;
        (let uu___146_2492 = wl in
         {
           attempting = (uu___146_2492.attempting);
           wl_deferred = (uu___146_2492.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___146_2492.defer_ok);
           smt_ok = (uu___146_2492.smt_ok);
           tcenv = (uu___146_2492.tcenv)
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
            | (uu____2521,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2529 = FStar_Syntax_Util.mk_conj t1 f in
                Some uu____2529 in
          (let uu____2535 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2535
           then
             let uu____2536 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2537 =
               let uu____2538 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2538 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2536 uu____2537
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2563 =
    let uu____2567 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2567 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2563
    (FStar_Util.for_some
       (fun uu____2584  ->
          match uu____2584 with
          | (uv,uu____2588) -> FStar_Syntax_Unionfind.equiv uv (fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2621 = occurs wl uk t in Prims.op_Negation uu____2621 in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2626 =
         let uu____2627 = FStar_Syntax_Print.uvar_to_string (fst uk) in
         let uu____2628 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2627 uu____2628 in
       Some uu____2626) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2676 = occurs_check env wl uk t in
  match uu____2676 with
  | (occurs_ok,msg) ->
      let uu____2693 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2693, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2757 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2781  ->
            fun uu____2782  ->
              match (uu____2781, uu____2782) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2825 =
                    let uu____2826 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2826 in
                  if uu____2825
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2840 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2840
                     then
                       let uu____2847 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____2847)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2757 with | (isect,uu____2869) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2922  ->
          fun uu____2923  ->
            match (uu____2922, uu____2923) with
            | ((a,uu____2933),(b,uu____2935)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2979 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2985  ->
                match uu____2985 with
                | (b,uu____2989) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____2979 then None else Some (a, (snd hd1))
  | uu____2998 -> None
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
            let uu____3041 = pat_var_opt env seen hd1 in
            (match uu____3041 with
             | None  ->
                 ((let uu____3049 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____3049
                   then
                     let uu____3050 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____3050
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3062 =
      let uu____3063 = FStar_Syntax_Subst.compress t in
      uu____3063.FStar_Syntax_Syntax.n in
    match uu____3062 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3066 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3075;
           FStar_Syntax_Syntax.tk = uu____3076;
           FStar_Syntax_Syntax.pos = uu____3077;
           FStar_Syntax_Syntax.vars = uu____3078;_},uu____3079)
        -> true
    | uu____3102 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3164;
         FStar_Syntax_Syntax.pos = uu____3165;
         FStar_Syntax_Syntax.vars = uu____3166;_},args)
      -> (t, uv, k, args)
  | uu____3207 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____3261 = destruct_flex_t t in
  match uu____3261 with
  | (t1,uv,k,args) ->
      let uu____3329 = pat_vars env [] args in
      (match uu____3329 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3385 -> ((t1, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth option*
  FStar_Syntax_Syntax.delta_depth option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3434 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth option* FStar_Syntax_Syntax.delta_depth
      option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3457 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3461 -> false
let head_match: match_result -> match_result =
  fun uu___123_3464  ->
    match uu___123_3464 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3473 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3486 ->
          let uu____3487 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3487 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3497 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3511 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3517 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> None
      | FStar_Syntax_Syntax.Tm_bvar uu____3539 -> None
      | FStar_Syntax_Syntax.Tm_name uu____3540 -> None
      | FStar_Syntax_Syntax.Tm_uvar uu____3541 -> None
      | FStar_Syntax_Syntax.Tm_let uu____3550 -> None
      | FStar_Syntax_Syntax.Tm_match uu____3558 -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3575) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3581,uu____3582) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3612) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3627;
             FStar_Syntax_Syntax.index = uu____3628;
             FStar_Syntax_Syntax.sort = t2;_},uu____3630)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3637 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3638 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3639 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3647 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3663 = fv_delta_depth env fv in Some uu____3663
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
            let uu____3682 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3682
            then FullMatch
            else
              (let uu____3684 =
                 let uu____3689 =
                   let uu____3691 = fv_delta_depth env f in Some uu____3691 in
                 let uu____3692 =
                   let uu____3694 = fv_delta_depth env g in Some uu____3694 in
                 (uu____3689, uu____3692) in
               MisMatch uu____3684)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3698),FStar_Syntax_Syntax.Tm_uinst (g,uu____3700)) ->
            let uu____3709 = head_matches env f g in
            FStar_All.pipe_right uu____3709 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3716),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3718)) ->
            let uu____3743 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____3743 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3748),FStar_Syntax_Syntax.Tm_refine (y,uu____3750)) ->
            let uu____3759 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3759 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3761),uu____3762) ->
            let uu____3767 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3767 head_match
        | (uu____3768,FStar_Syntax_Syntax.Tm_refine (x,uu____3770)) ->
            let uu____3775 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3775 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3776,FStar_Syntax_Syntax.Tm_type
           uu____3777) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3778,FStar_Syntax_Syntax.Tm_arrow uu____3779) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3795),FStar_Syntax_Syntax.Tm_app (head',uu____3797))
            ->
            let uu____3826 = head_matches env head1 head' in
            FStar_All.pipe_right uu____3826 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3828),uu____3829) ->
            let uu____3844 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____3844 head_match
        | (uu____3845,FStar_Syntax_Syntax.Tm_app (head1,uu____3847)) ->
            let uu____3862 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____3862 head_match
        | uu____3863 ->
            let uu____3866 =
              let uu____3871 = delta_depth_of_term env t11 in
              let uu____3873 = delta_depth_of_term env t21 in
              (uu____3871, uu____3873) in
            MisMatch uu____3866
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3909 = FStar_Syntax_Util.head_and_args t in
    match uu____3909 with
    | (head1,uu____3921) ->
        let uu____3936 =
          let uu____3937 = FStar_Syntax_Util.un_uinst head1 in
          uu____3937.FStar_Syntax_Syntax.n in
        (match uu____3936 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3942 =
               let uu____3943 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____3943 FStar_Option.isSome in
             if uu____3942
             then
               let uu____3957 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____3957 (fun _0_48  -> Some _0_48)
             else None
         | uu____3960 -> None) in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None)) in
  let fail r = (r, None) in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21 in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),uu____4028) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4038 =
             let uu____4043 = maybe_inline t11 in
             let uu____4045 = maybe_inline t21 in (uu____4043, uu____4045) in
           match uu____4038 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (uu____4066,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4076 =
             let uu____4081 = maybe_inline t11 in
             let uu____4083 = maybe_inline t21 in (uu____4081, uu____4083) in
           match uu____4076 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____4108 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____4108 with
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
        let uu____4123 =
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
             let uu____4131 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____4131)) in
        (match uu____4123 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4139 -> fail r
    | uu____4144 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4173 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4203 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4218 = FStar_Syntax_Util.type_u () in
      match uu____4218 with
      | (t,uu____4222) ->
          let uu____4223 = new_uvar r binders t in fst uu____4223
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4232 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____4232 FStar_Pervasives.fst
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
        let uu____4274 = head_matches env t1 t' in
        match uu____4274 with
        | MisMatch uu____4275 -> false
        | uu____4280 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4340,imp),T (t2,uu____4343)) -> (t2, imp)
                     | uu____4360 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4400  ->
                    match uu____4400 with
                    | (t2,uu____4408) ->
                        (None, INVARIANT, (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____4438 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____4438 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4491))::tcs2) ->
                       aux
                         (((let uu___147_4513 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___147_4513.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___147_4513.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4523 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___124_4554 =
                 match uu___124_4554 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4617 = decompose1 [] bs1 in
               (rebuild, matches, uu____4617))
      | uu____4645 ->
          let rebuild uu___125_4650 =
            match uu___125_4650 with
            | [] -> t1
            | uu____4652 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___126_4671  ->
    match uu___126_4671 with
    | T (t,uu____4673) -> t
    | uu____4682 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___127_4685  ->
    match uu___127_4685 with
    | T (t,uu____4687) -> FStar_Syntax_Syntax.as_arg t
    | uu____4696 -> failwith "Impossible"
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
              | (uu____4765,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4784 = new_uvar r scope1 k in
                  (match uu____4784 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4796 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args)) None r in
                       let uu____4811 =
                         let uu____4812 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_49  ->
                              FStar_TypeChecker_Common.TProb _0_49)
                           uu____4812 in
                       ((T (gi_xs, mk_kind)), uu____4811))
              | (uu____4821,uu____4822,C uu____4823) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4910 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4921;
                         FStar_Syntax_Syntax.pos = uu____4922;
                         FStar_Syntax_Syntax.vars = uu____4923;_})
                        ->
                        let uu____4938 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4938 with
                         | (T (gi_xs,uu____4954),prob) ->
                             let uu____4964 =
                               let uu____4965 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_50  -> C _0_50)
                                 uu____4965 in
                             (uu____4964, [prob])
                         | uu____4967 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4977;
                         FStar_Syntax_Syntax.pos = uu____4978;
                         FStar_Syntax_Syntax.vars = uu____4979;_})
                        ->
                        let uu____4994 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4994 with
                         | (T (gi_xs,uu____5010),prob) ->
                             let uu____5020 =
                               let uu____5021 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_51  -> C _0_51)
                                 uu____5021 in
                             (uu____5020, [prob])
                         | uu____5023 -> failwith "impossible")
                    | (uu____5029,uu____5030,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____5032;
                         FStar_Syntax_Syntax.pos = uu____5033;
                         FStar_Syntax_Syntax.vars = uu____5034;_})
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
                        let uu____5108 =
                          let uu____5113 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____5113 FStar_List.unzip in
                        (match uu____5108 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5142 =
                                 let uu____5143 =
                                   let uu____5146 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____5146 un_T in
                                 let uu____5147 =
                                   let uu____5153 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____5153
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5143;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5147;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5142 in
                             ((C gi_xs), sub_probs))
                    | uu____5158 ->
                        let uu____5165 = sub_prob scope1 args q in
                        (match uu____5165 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____4910 with
                   | (tc,probs) ->
                       let uu____5183 =
                         match q with
                         | (Some b,uu____5209,uu____5210) ->
                             let uu____5218 =
                               let uu____5222 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____5222 :: args in
                             ((Some b), (b :: scope1), uu____5218)
                         | uu____5240 -> (None, scope1, args) in
                       (match uu____5183 with
                        | (bopt,scope2,args1) ->
                            let uu____5283 = aux scope2 args1 qs2 in
                            (match uu____5283 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____5304 =
                                         let uu____5306 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         f :: uu____5306 in
                                       FStar_Syntax_Util.mk_conj_l uu____5304
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (fst b).FStar_Syntax_Syntax.sort in
                                       let uu____5319 =
                                         let uu____5321 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (fst b) f in
                                         let uu____5322 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         uu____5321 :: uu____5322 in
                                       FStar_Syntax_Util.mk_conj_l uu____5319 in
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
  let uu___148_5375 = p in
  let uu____5378 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____5379 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___148_5375.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5378;
    FStar_TypeChecker_Common.relation =
      (uu___148_5375.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5379;
    FStar_TypeChecker_Common.element =
      (uu___148_5375.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___148_5375.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___148_5375.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___148_5375.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___148_5375.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___148_5375.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5389 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____5389
            (fun _0_52  -> FStar_TypeChecker_Common.TProb _0_52)
      | FStar_TypeChecker_Common.CProb uu____5394 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5408 = compress_prob wl pr in
        FStar_All.pipe_right uu____5408 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5414 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____5414 with
           | (lh,uu____5427) ->
               let uu____5442 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____5442 with
                | (rh,uu____5455) ->
                    let uu____5470 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5479,FStar_Syntax_Syntax.Tm_uvar uu____5480)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5499,uu____5500)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5511,FStar_Syntax_Syntax.Tm_uvar uu____5512)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5523,uu____5524)
                          ->
                          let uu____5533 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5533 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5573 ->
                                    let rank =
                                      let uu____5580 = is_top_level_prob prob in
                                      if uu____5580
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5582 =
                                      let uu___149_5585 = tp in
                                      let uu____5588 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_5585.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___149_5585.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_5585.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5588;
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_5585.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_5585.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_5585.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_5585.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_5585.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_5585.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5582)))
                      | (uu____5598,FStar_Syntax_Syntax.Tm_uvar uu____5599)
                          ->
                          let uu____5608 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5608 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5648 ->
                                    let uu____5654 =
                                      let uu___150_5659 = tp in
                                      let uu____5662 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___150_5659.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5662;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___150_5659.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___150_5659.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___150_5659.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___150_5659.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___150_5659.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___150_5659.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___150_5659.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___150_5659.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5654)))
                      | (uu____5678,uu____5679) -> (rigid_rigid, tp) in
                    (match uu____5470 with
                     | (rank,tp1) ->
                         let uu____5690 =
                           FStar_All.pipe_right
                             (let uu___151_5693 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___151_5693.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___151_5693.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___151_5693.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___151_5693.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___151_5693.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___151_5693.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___151_5693.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___151_5693.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___151_5693.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_53  ->
                                FStar_TypeChecker_Common.TProb _0_53) in
                         (rank, uu____5690))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5699 =
            FStar_All.pipe_right
              (let uu___152_5702 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___152_5702.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___152_5702.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___152_5702.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___152_5702.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___152_5702.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___152_5702.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___152_5702.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___152_5702.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___152_5702.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_54  -> FStar_TypeChecker_Common.CProb _0_54) in
          (rigid_rigid, uu____5699)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob option* FStar_TypeChecker_Common.prob
      Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____5734 probs =
      match uu____5734 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5764 = rank wl hd1 in
               (match uu____5764 with
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
    match projectee with | UDeferred _0 -> true | uu____5832 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5844 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5856 -> false
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
                        let uu____5889 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____5889 with
                        | (k,uu____5893) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____5897 -> false)))
            | uu____5898 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____5945 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____5945 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5948 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____5954 =
                     let uu____5955 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____5956 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5955
                       uu____5956 in
                   UFailed uu____5954)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5972 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5972 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5990 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5990 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____5993 ->
                let uu____5996 =
                  let uu____5997 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____5998 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5997
                    uu____5998 msg in
                UFailed uu____5996 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____5999,uu____6000) ->
              let uu____6001 =
                let uu____6002 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6003 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6002 uu____6003 in
              failwith uu____6001
          | (FStar_Syntax_Syntax.U_unknown ,uu____6004) ->
              let uu____6005 =
                let uu____6006 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6007 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6006 uu____6007 in
              failwith uu____6005
          | (uu____6008,FStar_Syntax_Syntax.U_bvar uu____6009) ->
              let uu____6010 =
                let uu____6011 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6012 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6011 uu____6012 in
              failwith uu____6010
          | (uu____6013,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____6014 =
                let uu____6015 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6016 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6015 uu____6016 in
              failwith uu____6014
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____6028 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____6028
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____6038 = occurs_univ v1 u3 in
              if uu____6038
              then
                let uu____6039 =
                  let uu____6040 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6041 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6040 uu____6041 in
                try_umax_components u11 u21 uu____6039
              else
                (let uu____6043 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6043)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____6051 = occurs_univ v1 u3 in
              if uu____6051
              then
                let uu____6052 =
                  let uu____6053 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6054 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6053 uu____6054 in
                try_umax_components u11 u21 uu____6052
              else
                (let uu____6056 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6056)
          | (FStar_Syntax_Syntax.U_max uu____6059,uu____6060) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6065 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6065
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____6067,FStar_Syntax_Syntax.U_max uu____6068) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6073 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6073
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6075,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6076,FStar_Syntax_Syntax.U_name
             uu____6077) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6078) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6079) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6080,FStar_Syntax_Syntax.U_succ
             uu____6081) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6082,FStar_Syntax_Syntax.U_zero
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
  let uu____6144 = bc1 in
  match uu____6144 with
  | (bs1,mk_cod1) ->
      let uu____6169 = bc2 in
      (match uu____6169 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6216 = FStar_Util.first_N n1 bs in
             match uu____6216 with
             | (bs3,rest) ->
                 let uu____6230 = mk_cod rest in (bs3, uu____6230) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____6254 =
               let uu____6258 = mk_cod1 [] in (bs1, uu____6258) in
             let uu____6260 =
               let uu____6264 = mk_cod2 [] in (bs2, uu____6264) in
             (uu____6254, uu____6260)
           else
             if l1 > l2
             then
               (let uu____6291 = curry l2 bs1 mk_cod1 in
                let uu____6301 =
                  let uu____6305 = mk_cod2 [] in (bs2, uu____6305) in
                (uu____6291, uu____6301))
             else
               (let uu____6314 =
                  let uu____6318 = mk_cod1 [] in (bs1, uu____6318) in
                let uu____6320 = curry l1 bs2 mk_cod2 in
                (uu____6314, uu____6320)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6427 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____6427
       then
         let uu____6428 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6428
       else ());
      (let uu____6430 = next_prob probs in
       match uu____6430 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___153_6443 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___153_6443.wl_deferred);
               ctr = (uu___153_6443.ctr);
               defer_ok = (uu___153_6443.defer_ok);
               smt_ok = (uu___153_6443.smt_ok);
               tcenv = (uu___153_6443.tcenv)
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
                  let uu____6450 = solve_flex_rigid_join env tp probs1 in
                  (match uu____6450 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6454 = solve_rigid_flex_meet env tp probs1 in
                     match uu____6454 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____6458,uu____6459) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6468 ->
                let uu____6473 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6501  ->
                          match uu____6501 with
                          | (c,uu____6506,uu____6507) -> c < probs.ctr)) in
                (match uu____6473 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6529 =
                            FStar_List.map
                              (fun uu____6535  ->
                                 match uu____6535 with
                                 | (uu____6541,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____6529
                      | uu____6544 ->
                          let uu____6549 =
                            let uu___154_6550 = probs in
                            let uu____6551 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6560  ->
                                      match uu____6560 with
                                      | (uu____6564,uu____6565,y) -> y)) in
                            {
                              attempting = uu____6551;
                              wl_deferred = rest;
                              ctr = (uu___154_6550.ctr);
                              defer_ok = (uu___154_6550.defer_ok);
                              smt_ok = (uu___154_6550.smt_ok);
                              tcenv = (uu___154_6550.tcenv)
                            } in
                          solve env uu____6549))))
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
            let uu____6572 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____6572 with
            | USolved wl1 ->
                let uu____6574 = solve_prob orig None [] wl1 in
                solve env uu____6574
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
                  let uu____6608 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6608 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6611 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6619;
                  FStar_Syntax_Syntax.pos = uu____6620;
                  FStar_Syntax_Syntax.vars = uu____6621;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6624;
                  FStar_Syntax_Syntax.pos = uu____6625;
                  FStar_Syntax_Syntax.vars = uu____6626;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6638,uu____6639) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6644,FStar_Syntax_Syntax.Tm_uinst uu____6645) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6650 -> USolved wl
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
            ((let uu____6658 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6658
              then
                let uu____6659 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6659 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6667 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6667
         then
           let uu____6668 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6668
         else ());
        (let uu____6670 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6670 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6712 = head_matches_delta env () t1 t2 in
               match uu____6712 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6734 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6760 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6769 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____6770 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____6769, uu____6770)
                          | None  ->
                              let uu____6773 = FStar_Syntax_Subst.compress t1 in
                              let uu____6774 = FStar_Syntax_Subst.compress t2 in
                              (uu____6773, uu____6774) in
                        (match uu____6760 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6796 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_55  ->
                                    FStar_TypeChecker_Common.TProb _0_55)
                                 uu____6796 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6819 =
                                    let uu____6825 =
                                      let uu____6828 =
                                        let uu____6831 =
                                          let uu____6832 =
                                            let uu____6837 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____6837) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6832 in
                                        FStar_Syntax_Syntax.mk uu____6831 in
                                      uu____6828 None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____6850 =
                                      let uu____6852 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____6852] in
                                    (uu____6825, uu____6850) in
                                  Some uu____6819
                              | (uu____6861,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6863)) ->
                                  let uu____6868 =
                                    let uu____6872 =
                                      let uu____6874 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____6874] in
                                    (t11, uu____6872) in
                                  Some uu____6868
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6880),uu____6881) ->
                                  let uu____6886 =
                                    let uu____6890 =
                                      let uu____6892 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____6892] in
                                    (t21, uu____6890) in
                                  Some uu____6886
                              | uu____6897 ->
                                  let uu____6900 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____6900 with
                                   | (head1,uu____6915) ->
                                       let uu____6930 =
                                         let uu____6931 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____6931.FStar_Syntax_Syntax.n in
                                       (match uu____6930 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6938;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6940;_}
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
                                        | uu____6949 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6958) ->
                  let uu____6971 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___128_6980  ->
                            match uu___128_6980 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6985 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____6985 with
                                      | (u',uu____6996) ->
                                          let uu____7011 =
                                            let uu____7012 = whnf env u' in
                                            uu____7012.FStar_Syntax_Syntax.n in
                                          (match uu____7011 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____7016) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____7029 -> false))
                                 | uu____7030 -> false)
                            | uu____7032 -> false)) in
                  (match uu____6971 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____7053 tps =
                         match uu____7053 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7080 =
                                    let uu____7085 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____7085 in
                                  (match uu____7080 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____7104 -> None) in
                       let uu____7109 =
                         let uu____7114 =
                           let uu____7118 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____7118, []) in
                         make_lower_bound uu____7114 lower_bounds in
                       (match uu____7109 with
                        | None  ->
                            ((let uu____7125 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7125
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
                            ((let uu____7138 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7138
                              then
                                let wl' =
                                  let uu___155_7140 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___155_7140.wl_deferred);
                                    ctr = (uu___155_7140.ctr);
                                    defer_ok = (uu___155_7140.defer_ok);
                                    smt_ok = (uu___155_7140.smt_ok);
                                    tcenv = (uu___155_7140.tcenv)
                                  } in
                                let uu____7141 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7141
                              else ());
                             (let uu____7143 =
                                solve_t env eq_prob
                                  (let uu___156_7144 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___156_7144.wl_deferred);
                                     ctr = (uu___156_7144.ctr);
                                     defer_ok = (uu___156_7144.defer_ok);
                                     smt_ok = (uu___156_7144.smt_ok);
                                     tcenv = (uu___156_7144.tcenv)
                                   }) in
                              match uu____7143 with
                              | Success uu____7146 ->
                                  let wl1 =
                                    let uu___157_7148 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___157_7148.wl_deferred);
                                      ctr = (uu___157_7148.ctr);
                                      defer_ok = (uu___157_7148.defer_ok);
                                      smt_ok = (uu___157_7148.smt_ok);
                                      tcenv = (uu___157_7148.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1 in
                                  let uu____7150 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds in
                                  Some wl2
                              | uu____7153 -> None))))
              | uu____7154 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7161 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____7161
         then
           let uu____7162 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7162
         else ());
        (let uu____7164 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____7164 with
         | (u,args) ->
             let uu____7191 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____7191 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____7222 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____7222 with
                    | (h1,args1) ->
                        let uu____7250 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____7250 with
                         | (h2,uu____7263) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7282 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____7282
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7297 =
                                          let uu____7299 =
                                            let uu____7300 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_56  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_56) uu____7300 in
                                          [uu____7299] in
                                        Some uu____7297))
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
                                       (let uu____7324 =
                                          let uu____7326 =
                                            let uu____7327 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_57  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_57) uu____7327 in
                                          [uu____7326] in
                                        Some uu____7324))
                                  else None
                              | uu____7335 -> None)) in
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
                             let uu____7401 =
                               let uu____7407 =
                                 let uu____7410 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____7410 in
                               (uu____7407, m1) in
                             Some uu____7401)
                    | (uu____7419,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7421)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7453),uu____7454) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____7485 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7519) ->
                       let uu____7532 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___129_7541  ->
                                 match uu___129_7541 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____7546 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____7546 with
                                           | (u',uu____7557) ->
                                               let uu____7572 =
                                                 let uu____7573 = whnf env u' in
                                                 uu____7573.FStar_Syntax_Syntax.n in
                                               (match uu____7572 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7577) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____7590 -> false))
                                      | uu____7591 -> false)
                                 | uu____7593 -> false)) in
                       (match uu____7532 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7618 tps =
                              match uu____7618 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7659 =
                                         let uu____7666 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7666 in
                                       (match uu____7659 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7701 -> None) in
                            let uu____7708 =
                              let uu____7715 =
                                let uu____7721 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7721, []) in
                              make_upper_bound uu____7715 upper_bounds in
                            (match uu____7708 with
                             | None  ->
                                 ((let uu____7730 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7730
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
                                 ((let uu____7749 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7749
                                   then
                                     let wl' =
                                       let uu___158_7751 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___158_7751.wl_deferred);
                                         ctr = (uu___158_7751.ctr);
                                         defer_ok = (uu___158_7751.defer_ok);
                                         smt_ok = (uu___158_7751.smt_ok);
                                         tcenv = (uu___158_7751.tcenv)
                                       } in
                                     let uu____7752 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7752
                                   else ());
                                  (let uu____7754 =
                                     solve_t env eq_prob
                                       (let uu___159_7755 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___159_7755.wl_deferred);
                                          ctr = (uu___159_7755.ctr);
                                          defer_ok = (uu___159_7755.defer_ok);
                                          smt_ok = (uu___159_7755.smt_ok);
                                          tcenv = (uu___159_7755.tcenv)
                                        }) in
                                   match uu____7754 with
                                   | Success uu____7757 ->
                                       let wl1 =
                                         let uu___160_7759 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___160_7759.wl_deferred);
                                           ctr = (uu___160_7759.ctr);
                                           defer_ok =
                                             (uu___160_7759.defer_ok);
                                           smt_ok = (uu___160_7759.smt_ok);
                                           tcenv = (uu___160_7759.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1 in
                                       let uu____7761 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds in
                                       Some wl2
                                   | uu____7764 -> None))))
                   | uu____7765 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____7830 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____7830
                      then
                        let uu____7831 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7831
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___161_7863 = hd1 in
                      let uu____7864 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_7863.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_7863.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7864
                      } in
                    let hd21 =
                      let uu___162_7868 = hd2 in
                      let uu____7869 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___162_7868.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___162_7868.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7869
                      } in
                    let prob =
                      let uu____7873 =
                        let uu____7876 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7876 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_58  -> FStar_TypeChecker_Common.TProb _0_58)
                        uu____7873 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____7884 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7884 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____7887 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____7887 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7905 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives.fst in
                           let uu____7908 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____7905 uu____7908 in
                         ((let uu____7914 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____7914
                           then
                             let uu____7915 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____7916 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7915 uu____7916
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7931 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____7937 = aux scope env [] bs1 bs2 in
              match uu____7937 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7953 = compress_tprob wl problem in
        solve_t' env uu____7953 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7986 = head_matches_delta env1 wl1 t1 t2 in
          match uu____7986 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____8003,uu____8004) ->
                   let may_relate head3 =
                     let uu____8019 =
                       let uu____8020 = FStar_Syntax_Util.un_uinst head3 in
                       uu____8020.FStar_Syntax_Syntax.n in
                     match uu____8019 with
                     | FStar_Syntax_Syntax.Tm_name uu____8023 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____8024 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____8041 -> false in
                   let uu____8042 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____8042
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
                                let uu____8059 =
                                  let uu____8060 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____8060 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____8059 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____8062 = solve_prob orig (Some guard) [] wl1 in
                     solve env1 uu____8062
                   else
                     (let uu____8064 =
                        let uu____8065 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____8066 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____8065 uu____8066 in
                      giveup env1 uu____8064 orig)
               | (uu____8067,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___163_8075 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___163_8075.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___163_8075.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___163_8075.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___163_8075.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___163_8075.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___163_8075.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___163_8075.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___163_8075.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____8076,None ) ->
                   ((let uu____8083 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8083
                     then
                       let uu____8084 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____8085 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____8086 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____8087 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____8084
                         uu____8085 uu____8086 uu____8087
                     else ());
                    (let uu____8089 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____8089 with
                     | (head11,args1) ->
                         let uu____8115 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____8115 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8160 =
                                  let uu____8161 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____8162 = args_to_string args1 in
                                  let uu____8163 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____8164 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8161 uu____8162 uu____8163
                                    uu____8164 in
                                giveup env1 uu____8160 orig
                              else
                                (let uu____8166 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8171 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____8171 = FStar_Syntax_Util.Equal) in
                                 if uu____8166
                                 then
                                   let uu____8172 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____8172 with
                                   | USolved wl2 ->
                                       let uu____8174 =
                                         solve_prob orig None [] wl2 in
                                       solve env1 uu____8174
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8178 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____8178 with
                                    | (base1,refinement1) ->
                                        let uu____8204 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____8204 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____8258 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____8258 with
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
                                                           (fun uu____8268 
                                                              ->
                                                              fun uu____8269 
                                                                ->
                                                                match 
                                                                  (uu____8268,
                                                                    uu____8269)
                                                                with
                                                                | ((a,uu____8279),
                                                                   (a',uu____8281))
                                                                    ->
                                                                    let uu____8286
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
                                                                    uu____8286)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____8292 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8292 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8296 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___164_8329 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___164_8329.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___164_8329.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___164_8329.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___164_8329.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___164_8329.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___164_8329.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___164_8329.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___164_8329.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____8349 = p in
          match uu____8349 with
          | (((u,k),xs,c),ps,(h,uu____8360,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8409 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____8409 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8423 = h gs_xs in
                     let uu____8424 =
                       let uu____8431 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_60  -> FStar_Util.Inl _0_60) in
                       FStar_All.pipe_right uu____8431
                         (fun _0_61  -> Some _0_61) in
                     FStar_Syntax_Util.abs xs1 uu____8423 uu____8424 in
                   ((let uu____8462 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8462
                     then
                       let uu____8463 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____8464 = FStar_Syntax_Print.comp_to_string c in
                       let uu____8465 = FStar_Syntax_Print.term_to_string im in
                       let uu____8466 = FStar_Syntax_Print.tag_of_term im in
                       let uu____8467 =
                         let uu____8468 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____8468
                           (FStar_String.concat ", ") in
                       let uu____8471 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8463 uu____8464 uu____8465 uu____8466
                         uu____8467 uu____8471
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___130_8489 =
          match uu___130_8489 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____8518 = p in
          match uu____8518 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8576 = FStar_List.nth ps i in
              (match uu____8576 with
               | (pi,uu____8579) ->
                   let uu____8584 = FStar_List.nth xs i in
                   (match uu____8584 with
                    | (xi,uu____8591) ->
                        let rec gs k =
                          let uu____8600 = FStar_Syntax_Util.arrow_formals k in
                          match uu____8600 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8652)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8660 = new_uvar r xs k_a in
                                    (match uu____8660 with
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
                                         let uu____8679 = aux subst2 tl1 in
                                         (match uu____8679 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8694 =
                                                let uu____8696 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8696 :: gi_xs' in
                                              let uu____8697 =
                                                let uu____8699 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8699 :: gi_ps' in
                                              (uu____8694, uu____8697))) in
                              aux [] bs in
                        let uu____8702 =
                          let uu____8703 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8703 in
                        if uu____8702
                        then None
                        else
                          (let uu____8706 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8706 with
                           | (g_xs,uu____8713) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8720 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r in
                                 let uu____8725 =
                                   let uu____8732 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_62  -> FStar_Util.Inl _0_62) in
                                   FStar_All.pipe_right uu____8732
                                     (fun _0_63  -> Some _0_63) in
                                 FStar_Syntax_Util.abs xs uu____8720
                                   uu____8725 in
                               let sub1 =
                                 let uu____8763 =
                                   let uu____8766 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let uu____8773 =
                                     let uu____8776 =
                                       FStar_List.map
                                         (fun uu____8782  ->
                                            match uu____8782 with
                                            | (uu____8787,uu____8788,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____8776 in
                                   mk_problem (p_scope orig) orig uu____8766
                                     (p_rel orig) uu____8773 None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____8763 in
                               ((let uu____8798 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____8798
                                 then
                                   let uu____8799 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____8800 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8799 uu____8800
                                 else ());
                                (let wl2 =
                                   let uu____8803 =
                                     let uu____8805 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives.fst (p_guard sub1) in
                                     Some uu____8805 in
                                   solve_prob orig uu____8803
                                     [TERM (u, proj)] wl1 in
                                 let uu____8810 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_65  -> Some _0_65) uu____8810))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8834 = lhs in
          match uu____8834 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8857 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____8857 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8883 =
                        let uu____8909 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____8909) in
                      Some uu____8883
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____8992 =
                           let uu____8996 =
                             let uu____8997 = FStar_Syntax_Subst.compress k in
                             uu____8997.FStar_Syntax_Syntax.n in
                           (uu____8996, args) in
                         match uu____8992 with
                         | (uu____9004,[]) ->
                             let uu____9006 =
                               let uu____9012 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____9012) in
                             Some uu____9006
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____9023,uu____9024) ->
                             let uu____9035 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9035 with
                              | (uv1,uv_args) ->
                                  let uu____9064 =
                                    let uu____9065 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9065.FStar_Syntax_Syntax.n in
                                  (match uu____9064 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9072) ->
                                       let uu____9085 =
                                         pat_vars env [] uv_args in
                                       (match uu____9085 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9099  ->
                                                      let uu____9100 =
                                                        let uu____9101 =
                                                          let uu____9102 =
                                                            let uu____9105 =
                                                              let uu____9106
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9106
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9105 in
                                                          fst uu____9102 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9101 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9100)) in
                                            let c1 =
                                              let uu____9112 =
                                                let uu____9113 =
                                                  let uu____9116 =
                                                    let uu____9117 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9117
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9116 in
                                                fst uu____9113 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9112 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9126 =
                                                let uu____9133 =
                                                  let uu____9139 =
                                                    let uu____9140 =
                                                      let uu____9143 =
                                                        let uu____9144 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9144
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9143 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9140 in
                                                  FStar_Util.Inl uu____9139 in
                                                Some uu____9133 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9126 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9164 -> None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9167,uu____9168)
                             ->
                             let uu____9180 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9180 with
                              | (uv1,uv_args) ->
                                  let uu____9209 =
                                    let uu____9210 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9210.FStar_Syntax_Syntax.n in
                                  (match uu____9209 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9217) ->
                                       let uu____9230 =
                                         pat_vars env [] uv_args in
                                       (match uu____9230 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9244  ->
                                                      let uu____9245 =
                                                        let uu____9246 =
                                                          let uu____9247 =
                                                            let uu____9250 =
                                                              let uu____9251
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9251
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9250 in
                                                          fst uu____9247 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9246 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9245)) in
                                            let c1 =
                                              let uu____9257 =
                                                let uu____9258 =
                                                  let uu____9261 =
                                                    let uu____9262 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9262
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9261 in
                                                fst uu____9258 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9257 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9271 =
                                                let uu____9278 =
                                                  let uu____9284 =
                                                    let uu____9285 =
                                                      let uu____9288 =
                                                        let uu____9289 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9289
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9288 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9285 in
                                                  FStar_Util.Inl uu____9284 in
                                                Some uu____9278 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9271 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9309 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9314)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____9346 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____9346
                                 (fun _0_66  -> Some _0_66)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9370 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____9370 with
                                  | (args1,rest) ->
                                      let uu____9388 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____9388 with
                                       | (xs2,c2) ->
                                           let uu____9396 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____9396
                                             (fun uu____9407  ->
                                                match uu____9407 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9429 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____9429 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____9477 =
                                        let uu____9480 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9480 in
                                      FStar_All.pipe_right uu____9477
                                        (fun _0_67  -> Some _0_67))
                         | uu____9488 ->
                             let uu____9492 =
                               let uu____9493 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____9494 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____9495 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9493 uu____9494 uu____9495 in
                             failwith uu____9492 in
                       let uu____9499 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____9499
                         (fun uu____9527  ->
                            match uu____9527 with
                            | (xs1,c1) ->
                                let uu____9555 =
                                  let uu____9578 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9578) in
                                Some uu____9555)) in
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
                     let uu____9650 = imitate orig env wl1 st in
                     match uu____9650 with
                     | Failed uu____9655 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9661 = project orig env wl1 i st in
                      match uu____9661 with
                      | None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some (Failed uu____9668) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____9682 = FStar_Syntax_Util.head_and_args t21 in
                match uu____9682 with
                | (hd1,uu____9693) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9708 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9716 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9717 -> true
                     | uu____9732 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____9735 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____9735
                         then true
                         else
                           ((let uu____9738 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____9738
                             then
                               let uu____9739 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9739
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9747 =
                    let uu____9750 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____9750 FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____9747 FStar_Syntax_Free.names in
                let uu____9781 = FStar_Util.set_is_empty fvs_hd in
                if uu____9781
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____9790 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____9790 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9798 =
                            let uu____9799 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____9799 in
                          giveup_or_defer1 orig uu____9798
                        else
                          (let uu____9801 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____9801
                           then
                             let uu____9802 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____9802
                              then
                                let uu____9803 = subterms args_lhs in
                                imitate' orig env wl1 uu____9803
                              else
                                ((let uu____9807 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____9807
                                  then
                                    let uu____9808 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____9809 = names_to_string fvs1 in
                                    let uu____9810 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9808 uu____9809 uu____9810
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9815 ->
                                        let uu____9816 = sn_binders env vars in
                                        u_abs k_uv uu____9816 t21 in
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
                               (let uu____9825 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____9825
                                then
                                  ((let uu____9827 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____9827
                                    then
                                      let uu____9828 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____9829 = names_to_string fvs1 in
                                      let uu____9830 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9828 uu____9829 uu____9830
                                    else ());
                                   (let uu____9832 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9832
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
                     (let uu____9846 =
                        let uu____9847 = FStar_Syntax_Free.names t1 in
                        check_head uu____9847 t2 in
                      if uu____9846
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____9851 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____9851
                          then
                            let uu____9852 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9852
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9855 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9855 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9900 =
               match uu____9900 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k in
                   let uu____9931 = FStar_Syntax_Util.arrow_formals k1 in
                   (match uu____9931 with
                    | (all_formals,uu____9942) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____10034  ->
                                        match uu____10034 with
                                        | (x,imp) ->
                                            let uu____10041 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____10041, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____10049 = FStar_Syntax_Util.type_u () in
                                match uu____10049 with
                                | (t1,uu____10053) ->
                                    let uu____10054 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    fst uu____10054 in
                              let uu____10057 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____10057 with
                               | (t',tm_u1) ->
                                   let uu____10064 = destruct_flex_t t' in
                                   (match uu____10064 with
                                    | (uu____10084,u1,k11,uu____10087) ->
                                        let sol =
                                          let uu____10115 =
                                            let uu____10120 =
                                              u_abs k1 all_formals t' in
                                            ((u, k1), uu____10120) in
                                          TERM uu____10115 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10180 = pat_var_opt env pat_args hd1 in
                              (match uu____10180 with
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
                                              (fun uu____10209  ->
                                                 match uu____10209 with
                                                 | (x,uu____10213) ->
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
                                      let uu____10219 =
                                        let uu____10220 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____10220 in
                                      if uu____10219
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10224 =
                                           FStar_Util.set_add (fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10224 formals1
                                           tl1)))
                          | uu____10230 -> failwith "Impossible" in
                        let uu____10241 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____10241 all_formals args) in
             let solve_both_pats wl1 uu____10281 uu____10282 r =
               match (uu____10281, uu____10282) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10396 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____10396
                   then
                     let uu____10397 = solve_prob orig None [] wl1 in
                     solve env uu____10397
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____10412 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____10412
                       then
                         let uu____10413 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____10414 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____10415 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____10416 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____10417 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10413 uu____10414 uu____10415 uu____10416
                           uu____10417
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____10465 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____10465 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10478 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____10478 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10510 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10510 in
                                  let uu____10513 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____10513 k3)
                           else
                             (let uu____10516 =
                                let uu____10517 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____10518 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____10519 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10517 uu____10518 uu____10519 in
                              failwith uu____10516) in
                       let uu____10520 =
                         let uu____10526 =
                           let uu____10534 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____10534 in
                         match uu____10526 with
                         | (bs,k1') ->
                             let uu____10552 =
                               let uu____10560 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____10560 in
                             (match uu____10552 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____10581 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_68  ->
                                         FStar_TypeChecker_Common.TProb _0_68)
                                      uu____10581 in
                                  let uu____10586 =
                                    let uu____10589 =
                                      let uu____10590 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____10590.FStar_Syntax_Syntax.n in
                                    let uu____10593 =
                                      let uu____10594 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____10594.FStar_Syntax_Syntax.n in
                                    (uu____10589, uu____10593) in
                                  (match uu____10586 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10602,uu____10603) ->
                                       (k1', [sub_prob])
                                   | (uu____10607,FStar_Syntax_Syntax.Tm_type
                                      uu____10608) -> (k2', [sub_prob])
                                   | uu____10612 ->
                                       let uu____10615 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____10615 with
                                        | (t,uu____10624) ->
                                            let uu____10625 = new_uvar r zs t in
                                            (match uu____10625 with
                                             | (k_zs,uu____10634) ->
                                                 let kprob =
                                                   let uu____10636 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_69  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_69) uu____10636 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____10520 with
                       | (k_u',sub_probs) ->
                           let uu____10650 =
                             let uu____10658 =
                               let uu____10659 = new_uvar r zs k_u' in
                               FStar_All.pipe_left FStar_Pervasives.fst
                                 uu____10659 in
                             let uu____10664 =
                               let uu____10667 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____10667 in
                             let uu____10670 =
                               let uu____10673 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____10673 in
                             (uu____10658, uu____10664, uu____10670) in
                           (match uu____10650 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____10692 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____10692 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____10704 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____10704
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____10708 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____10708 with
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
             let solve_one_pat uu____10740 uu____10741 =
               match (uu____10740, uu____10741) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10805 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____10805
                     then
                       let uu____10806 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10807 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10806 uu____10807
                     else ());
                    (let uu____10809 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____10809
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10816  ->
                              fun uu____10817  ->
                                match (uu____10816, uu____10817) with
                                | ((a,uu____10827),(t21,uu____10829)) ->
                                    let uu____10834 =
                                      let uu____10837 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____10837
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____10834
                                      (fun _0_70  ->
                                         FStar_TypeChecker_Common.TProb _0_70))
                           xs args2 in
                       let guard =
                         let uu____10841 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____10841 in
                       let wl1 = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____10851 = occurs_check env wl (u1, k1) t21 in
                        match uu____10851 with
                        | (occurs_ok,uu____10856) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____10861 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____10861
                            then
                              let sol =
                                let uu____10863 =
                                  let uu____10868 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____10868) in
                                TERM uu____10863 in
                              let wl1 = solve_prob orig None [sol] wl in
                              solve env wl1
                            else
                              (let uu____10873 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____10873
                               then
                                 let uu____10874 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____10874 with
                                 | (sol,(uu____10884,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____10894 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____10894
                                       then
                                         let uu____10895 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10895
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10900 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____10902 = lhs in
             match uu____10902 with
             | (t1,u1,k1,args1) ->
                 let uu____10907 = rhs in
                 (match uu____10907 with
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
                       | uu____10933 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____10939 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____10939 with
                              | (sol,uu____10946) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____10949 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____10949
                                    then
                                      let uu____10950 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____10950
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____10955 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____10957 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____10957
        then
          let uu____10958 = solve_prob orig None [] wl in
          solve env uu____10958
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____10962 = FStar_Util.physical_equality t1 t2 in
           if uu____10962
           then
             let uu____10963 = solve_prob orig None [] wl in
             solve env uu____10963
           else
             ((let uu____10966 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____10966
               then
                 let uu____10967 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____10967
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____10970,uu____10971) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____10972,FStar_Syntax_Syntax.Tm_bvar uu____10973) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___131_11013 =
                     match uu___131_11013 with
                     | [] -> c
                     | bs ->
                         let uu____11027 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c)) None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____11027 in
                   let uu____11037 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____11037 with
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
                                   let uu____11123 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____11123
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____11125 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_71  ->
                                      FStar_TypeChecker_Common.CProb _0_71)
                                   uu____11125))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___132_11202 =
                     match uu___132_11202 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l)) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____11237 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____11237 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11320 =
                                   let uu____11323 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____11324 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____11323
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11324 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_72  ->
                                      FStar_TypeChecker_Common.TProb _0_72)
                                   uu____11320))
               | (FStar_Syntax_Syntax.Tm_abs uu____11327,uu____11328) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11351 -> true
                     | uu____11366 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11394 =
                     let uu____11405 = maybe_eta t1 in
                     let uu____11410 = maybe_eta t2 in
                     (uu____11405, uu____11410) in
                   (match uu____11394 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___165_11441 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___165_11441.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___165_11441.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___165_11441.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___165_11441.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___165_11441.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___165_11441.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___165_11441.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___165_11441.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11460 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11460
                        then
                          let uu____11461 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11461 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11482 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11482
                        then
                          let uu____11483 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11483 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11488 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11499,FStar_Syntax_Syntax.Tm_abs uu____11500) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11523 -> true
                     | uu____11538 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11566 =
                     let uu____11577 = maybe_eta t1 in
                     let uu____11582 = maybe_eta t2 in
                     (uu____11577, uu____11582) in
                   (match uu____11566 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___165_11613 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___165_11613.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___165_11613.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___165_11613.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___165_11613.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___165_11613.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___165_11613.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___165_11613.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___165_11613.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11632 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11632
                        then
                          let uu____11633 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11633 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11654 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11654
                        then
                          let uu____11655 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11655 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11660 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11671,FStar_Syntax_Syntax.Tm_refine uu____11672) ->
                   let uu____11681 = as_refinement env wl t1 in
                   (match uu____11681 with
                    | (x1,phi1) ->
                        let uu____11686 = as_refinement env wl t2 in
                        (match uu____11686 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11692 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_73  ->
                                    FStar_TypeChecker_Common.TProb _0_73)
                                 uu____11692 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____11725 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____11725
                                 (guard_on_element wl problem x11) in
                             let fallback uu____11729 =
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
                                 let uu____11735 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____11735 impl in
                               let wl1 = solve_prob orig (Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11742 =
                                   let uu____11745 =
                                     let uu____11746 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____11746 :: (p_scope orig) in
                                   mk_problem uu____11745 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_74  ->
                                      FStar_TypeChecker_Common.TProb _0_74)
                                   uu____11742 in
                               let uu____11749 =
                                 solve env1
                                   (let uu___166_11750 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___166_11750.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___166_11750.smt_ok);
                                      tcenv = (uu___166_11750.tcenv)
                                    }) in
                               (match uu____11749 with
                                | Failed uu____11754 -> fallback ()
                                | Success uu____11757 ->
                                    let guard =
                                      let uu____11761 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives.fst in
                                      let uu____11764 =
                                        let uu____11765 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives.fst in
                                        FStar_All.pipe_right uu____11765
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____11761
                                        uu____11764 in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl2 =
                                      let uu___167_11772 = wl1 in
                                      {
                                        attempting =
                                          (uu___167_11772.attempting);
                                        wl_deferred =
                                          (uu___167_11772.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___167_11772.defer_ok);
                                        smt_ok = (uu___167_11772.smt_ok);
                                        tcenv = (uu___167_11772.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11774,FStar_Syntax_Syntax.Tm_uvar uu____11775) ->
                   let uu____11792 = destruct_flex_t t1 in
                   let uu____11793 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11792 uu____11793
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11794;
                     FStar_Syntax_Syntax.tk = uu____11795;
                     FStar_Syntax_Syntax.pos = uu____11796;
                     FStar_Syntax_Syntax.vars = uu____11797;_},uu____11798),FStar_Syntax_Syntax.Tm_uvar
                  uu____11799) ->
                   let uu____11830 = destruct_flex_t t1 in
                   let uu____11831 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11830 uu____11831
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11832,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11833;
                     FStar_Syntax_Syntax.tk = uu____11834;
                     FStar_Syntax_Syntax.pos = uu____11835;
                     FStar_Syntax_Syntax.vars = uu____11836;_},uu____11837))
                   ->
                   let uu____11868 = destruct_flex_t t1 in
                   let uu____11869 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11868 uu____11869
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11870;
                     FStar_Syntax_Syntax.tk = uu____11871;
                     FStar_Syntax_Syntax.pos = uu____11872;
                     FStar_Syntax_Syntax.vars = uu____11873;_},uu____11874),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11875;
                     FStar_Syntax_Syntax.tk = uu____11876;
                     FStar_Syntax_Syntax.pos = uu____11877;
                     FStar_Syntax_Syntax.vars = uu____11878;_},uu____11879))
                   ->
                   let uu____11924 = destruct_flex_t t1 in
                   let uu____11925 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11924 uu____11925
               | (FStar_Syntax_Syntax.Tm_uvar uu____11926,uu____11927) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11936 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11936 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11940;
                     FStar_Syntax_Syntax.tk = uu____11941;
                     FStar_Syntax_Syntax.pos = uu____11942;
                     FStar_Syntax_Syntax.vars = uu____11943;_},uu____11944),uu____11945)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11968 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11968 t2 wl
               | (uu____11972,FStar_Syntax_Syntax.Tm_uvar uu____11973) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____11982,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11983;
                     FStar_Syntax_Syntax.tk = uu____11984;
                     FStar_Syntax_Syntax.pos = uu____11985;
                     FStar_Syntax_Syntax.vars = uu____11986;_},uu____11987))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12010,FStar_Syntax_Syntax.Tm_type uu____12011) ->
                   solve_t' env
                     (let uu___168_12020 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_12020.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_12020.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_12020.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_12020.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_12020.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_12020.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_12020.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_12020.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_12020.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12021;
                     FStar_Syntax_Syntax.tk = uu____12022;
                     FStar_Syntax_Syntax.pos = uu____12023;
                     FStar_Syntax_Syntax.vars = uu____12024;_},uu____12025),FStar_Syntax_Syntax.Tm_type
                  uu____12026) ->
                   solve_t' env
                     (let uu___168_12049 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_12049.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_12049.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_12049.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_12049.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_12049.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_12049.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_12049.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_12049.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_12049.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12050,FStar_Syntax_Syntax.Tm_arrow uu____12051) ->
                   solve_t' env
                     (let uu___168_12067 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_12067.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_12067.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_12067.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_12067.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_12067.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_12067.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_12067.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_12067.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_12067.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12068;
                     FStar_Syntax_Syntax.tk = uu____12069;
                     FStar_Syntax_Syntax.pos = uu____12070;
                     FStar_Syntax_Syntax.vars = uu____12071;_},uu____12072),FStar_Syntax_Syntax.Tm_arrow
                  uu____12073) ->
                   solve_t' env
                     (let uu___168_12103 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_12103.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_12103.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_12103.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_12103.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_12103.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_12103.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_12103.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_12103.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_12103.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____12104,uu____12105) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12116 =
                        let uu____12117 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12117 in
                      if uu____12116
                      then
                        let uu____12118 =
                          FStar_All.pipe_left
                            (fun _0_75  ->
                               FStar_TypeChecker_Common.TProb _0_75)
                            (let uu___169_12121 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_12121.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_12121.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_12121.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_12121.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_12121.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___169_12121.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_12121.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_12121.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_12121.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12122 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12118 uu____12122 t2
                          wl
                      else
                        (let uu____12127 = base_and_refinement env wl t2 in
                         match uu____12127 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12157 =
                                    FStar_All.pipe_left
                                      (fun _0_76  ->
                                         FStar_TypeChecker_Common.TProb _0_76)
                                      (let uu___170_12160 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___170_12160.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___170_12160.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___170_12160.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___170_12160.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___170_12160.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___170_12160.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___170_12160.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___170_12160.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___170_12160.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12161 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12157
                                    uu____12161 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___171_12176 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___171_12176.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___171_12176.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12179 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_77  ->
                                         FStar_TypeChecker_Common.TProb _0_77)
                                      uu____12179 in
                                  let guard =
                                    let uu____12187 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12187
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12193;
                     FStar_Syntax_Syntax.tk = uu____12194;
                     FStar_Syntax_Syntax.pos = uu____12195;
                     FStar_Syntax_Syntax.vars = uu____12196;_},uu____12197),uu____12198)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12223 =
                        let uu____12224 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12224 in
                      if uu____12223
                      then
                        let uu____12225 =
                          FStar_All.pipe_left
                            (fun _0_78  ->
                               FStar_TypeChecker_Common.TProb _0_78)
                            (let uu___169_12228 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_12228.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_12228.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_12228.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_12228.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_12228.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___169_12228.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_12228.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_12228.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_12228.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12229 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12225 uu____12229 t2
                          wl
                      else
                        (let uu____12234 = base_and_refinement env wl t2 in
                         match uu____12234 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12264 =
                                    FStar_All.pipe_left
                                      (fun _0_79  ->
                                         FStar_TypeChecker_Common.TProb _0_79)
                                      (let uu___170_12267 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___170_12267.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___170_12267.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___170_12267.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___170_12267.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___170_12267.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___170_12267.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___170_12267.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___170_12267.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___170_12267.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12268 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12264
                                    uu____12268 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___171_12283 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___171_12283.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___171_12283.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12286 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_80  ->
                                         FStar_TypeChecker_Common.TProb _0_80)
                                      uu____12286 in
                                  let guard =
                                    let uu____12294 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12294
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12300,FStar_Syntax_Syntax.Tm_uvar uu____12301) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12311 = base_and_refinement env wl t1 in
                      match uu____12311 with
                      | (t_base,uu____12322) ->
                          solve_t env
                            (let uu___172_12337 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___172_12337.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___172_12337.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___172_12337.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___172_12337.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___172_12337.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___172_12337.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___172_12337.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___172_12337.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12340,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12341;
                     FStar_Syntax_Syntax.tk = uu____12342;
                     FStar_Syntax_Syntax.pos = uu____12343;
                     FStar_Syntax_Syntax.vars = uu____12344;_},uu____12345))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12369 = base_and_refinement env wl t1 in
                      match uu____12369 with
                      | (t_base,uu____12380) ->
                          solve_t env
                            (let uu___172_12395 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___172_12395.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___172_12395.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___172_12395.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___172_12395.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___172_12395.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___172_12395.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___172_12395.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___172_12395.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12398,uu____12399) ->
                   let t21 =
                     let uu____12407 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____12407 in
                   solve_t env
                     (let uu___173_12420 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_12420.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___173_12420.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___173_12420.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___173_12420.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_12420.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_12420.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_12420.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_12420.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_12420.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12421,FStar_Syntax_Syntax.Tm_refine uu____12422) ->
                   let t11 =
                     let uu____12430 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____12430 in
                   solve_t env
                     (let uu___174_12443 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_12443.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___174_12443.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___174_12443.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___174_12443.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_12443.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_12443.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_12443.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_12443.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_12443.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12446,uu____12447) ->
                   let head1 =
                     let uu____12466 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12466 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12497 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12497 FStar_Pervasives.fst in
                   let uu____12525 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12525
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12534 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12534
                      then
                        let guard =
                          let uu____12541 =
                            let uu____12542 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12542 = FStar_Syntax_Util.Equal in
                          if uu____12541
                          then None
                          else
                            (let uu____12545 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_81  -> Some _0_81)
                               uu____12545) in
                        let uu____12547 = solve_prob orig guard [] wl in
                        solve env uu____12547
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12550,uu____12551) ->
                   let head1 =
                     let uu____12559 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12559 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12590 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12590 FStar_Pervasives.fst in
                   let uu____12618 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12618
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12627 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12627
                      then
                        let guard =
                          let uu____12634 =
                            let uu____12635 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12635 = FStar_Syntax_Util.Equal in
                          if uu____12634
                          then None
                          else
                            (let uu____12638 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_82  -> Some _0_82)
                               uu____12638) in
                        let uu____12640 = solve_prob orig guard [] wl in
                        solve env uu____12640
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12643,uu____12644) ->
                   let head1 =
                     let uu____12648 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12648 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12679 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12679 FStar_Pervasives.fst in
                   let uu____12707 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12707
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12716 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12716
                      then
                        let guard =
                          let uu____12723 =
                            let uu____12724 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12724 = FStar_Syntax_Util.Equal in
                          if uu____12723
                          then None
                          else
                            (let uu____12727 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_83  -> Some _0_83)
                               uu____12727) in
                        let uu____12729 = solve_prob orig guard [] wl in
                        solve env uu____12729
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12732,uu____12733) ->
                   let head1 =
                     let uu____12737 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12737 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12768 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12768 FStar_Pervasives.fst in
                   let uu____12796 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12796
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12805 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12805
                      then
                        let guard =
                          let uu____12812 =
                            let uu____12813 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12813 = FStar_Syntax_Util.Equal in
                          if uu____12812
                          then None
                          else
                            (let uu____12816 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_84  -> Some _0_84)
                               uu____12816) in
                        let uu____12818 = solve_prob orig guard [] wl in
                        solve env uu____12818
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____12821,uu____12822) ->
                   let head1 =
                     let uu____12826 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12826 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12857 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12857 FStar_Pervasives.fst in
                   let uu____12885 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12885
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12894 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12894
                      then
                        let guard =
                          let uu____12901 =
                            let uu____12902 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12902 = FStar_Syntax_Util.Equal in
                          if uu____12901
                          then None
                          else
                            (let uu____12905 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_85  -> Some _0_85)
                               uu____12905) in
                        let uu____12907 = solve_prob orig guard [] wl in
                        solve env uu____12907
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____12910,uu____12911) ->
                   let head1 =
                     let uu____12924 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12924 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12955 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12955 FStar_Pervasives.fst in
                   let uu____12983 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12983
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12992 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12992
                      then
                        let guard =
                          let uu____12999 =
                            let uu____13000 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13000 = FStar_Syntax_Util.Equal in
                          if uu____12999
                          then None
                          else
                            (let uu____13003 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_86  -> Some _0_86)
                               uu____13003) in
                        let uu____13005 = solve_prob orig guard [] wl in
                        solve env uu____13005
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13008,FStar_Syntax_Syntax.Tm_match uu____13009) ->
                   let head1 =
                     let uu____13028 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13028 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13059 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13059 FStar_Pervasives.fst in
                   let uu____13087 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13087
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13096 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13096
                      then
                        let guard =
                          let uu____13103 =
                            let uu____13104 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13104 = FStar_Syntax_Util.Equal in
                          if uu____13103
                          then None
                          else
                            (let uu____13107 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_87  -> Some _0_87)
                               uu____13107) in
                        let uu____13109 = solve_prob orig guard [] wl in
                        solve env uu____13109
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13112,FStar_Syntax_Syntax.Tm_uinst uu____13113) ->
                   let head1 =
                     let uu____13121 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13121 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13152 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13152 FStar_Pervasives.fst in
                   let uu____13180 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13180
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13189 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13189
                      then
                        let guard =
                          let uu____13196 =
                            let uu____13197 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13197 = FStar_Syntax_Util.Equal in
                          if uu____13196
                          then None
                          else
                            (let uu____13200 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_88  -> Some _0_88)
                               uu____13200) in
                        let uu____13202 = solve_prob orig guard [] wl in
                        solve env uu____13202
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13205,FStar_Syntax_Syntax.Tm_name uu____13206) ->
                   let head1 =
                     let uu____13210 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13210 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13241 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13241 FStar_Pervasives.fst in
                   let uu____13269 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13269
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13278 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13278
                      then
                        let guard =
                          let uu____13285 =
                            let uu____13286 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13286 = FStar_Syntax_Util.Equal in
                          if uu____13285
                          then None
                          else
                            (let uu____13289 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_89  -> Some _0_89)
                               uu____13289) in
                        let uu____13291 = solve_prob orig guard [] wl in
                        solve env uu____13291
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13294,FStar_Syntax_Syntax.Tm_constant uu____13295) ->
                   let head1 =
                     let uu____13299 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13299 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13330 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13330 FStar_Pervasives.fst in
                   let uu____13358 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13358
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13367 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13367
                      then
                        let guard =
                          let uu____13374 =
                            let uu____13375 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13375 = FStar_Syntax_Util.Equal in
                          if uu____13374
                          then None
                          else
                            (let uu____13378 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_90  -> Some _0_90)
                               uu____13378) in
                        let uu____13380 = solve_prob orig guard [] wl in
                        solve env uu____13380
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13383,FStar_Syntax_Syntax.Tm_fvar uu____13384) ->
                   let head1 =
                     let uu____13388 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13388 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13419 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13419 FStar_Pervasives.fst in
                   let uu____13447 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13447
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13456 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13456
                      then
                        let guard =
                          let uu____13463 =
                            let uu____13464 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13464 = FStar_Syntax_Util.Equal in
                          if uu____13463
                          then None
                          else
                            (let uu____13467 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_91  -> Some _0_91)
                               uu____13467) in
                        let uu____13469 = solve_prob orig guard [] wl in
                        solve env uu____13469
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13472,FStar_Syntax_Syntax.Tm_app uu____13473) ->
                   let head1 =
                     let uu____13486 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13486 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13517 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13517 FStar_Pervasives.fst in
                   let uu____13545 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13545
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13554 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13554
                      then
                        let guard =
                          let uu____13561 =
                            let uu____13562 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13562 = FStar_Syntax_Util.Equal in
                          if uu____13561
                          then None
                          else
                            (let uu____13565 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_92  -> Some _0_92)
                               uu____13565) in
                        let uu____13567 = solve_prob orig guard [] wl in
                        solve env uu____13567
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13571,uu____13572),uu____13573) ->
                   solve_t' env
                     (let uu___175_13602 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_13602.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_13602.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_13602.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_13602.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_13602.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_13602.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_13602.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_13602.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_13602.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13605,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13607,uu____13608)) ->
                   solve_t' env
                     (let uu___176_13637 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_13637.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___176_13637.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___176_13637.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___176_13637.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_13637.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_13637.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_13637.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_13637.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_13637.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13638,uu____13639) ->
                   let uu____13647 =
                     let uu____13648 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13649 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13648
                       uu____13649 in
                   failwith uu____13647
               | (FStar_Syntax_Syntax.Tm_meta uu____13650,uu____13651) ->
                   let uu____13656 =
                     let uu____13657 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13658 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13657
                       uu____13658 in
                   failwith uu____13656
               | (FStar_Syntax_Syntax.Tm_delayed uu____13659,uu____13660) ->
                   let uu____13681 =
                     let uu____13682 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13683 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13682
                       uu____13683 in
                   failwith uu____13681
               | (uu____13684,FStar_Syntax_Syntax.Tm_meta uu____13685) ->
                   let uu____13690 =
                     let uu____13691 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13692 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13691
                       uu____13692 in
                   failwith uu____13690
               | (uu____13693,FStar_Syntax_Syntax.Tm_delayed uu____13694) ->
                   let uu____13715 =
                     let uu____13716 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13717 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13716
                       uu____13717 in
                   failwith uu____13715
               | (uu____13718,FStar_Syntax_Syntax.Tm_let uu____13719) ->
                   let uu____13727 =
                     let uu____13728 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13729 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13728
                       uu____13729 in
                   failwith uu____13727
               | uu____13730 -> giveup env "head tag mismatch" orig)))
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
          (let uu____13762 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____13762
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____13770  ->
                  fun uu____13771  ->
                    match (uu____13770, uu____13771) with
                    | ((a1,uu____13781),(a2,uu____13783)) ->
                        let uu____13788 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_93  -> FStar_TypeChecker_Common.TProb _0_93)
                          uu____13788)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____13794 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p) FStar_Pervasives.fst)
                 sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____13794 in
           let wl1 = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____13814 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____13821)::[] -> wp1
              | uu____13834 ->
                  let uu____13840 =
                    let uu____13841 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____13841 in
                  failwith uu____13840 in
            let uu____13844 =
              let uu____13850 =
                let uu____13851 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____13851 in
              [uu____13850] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____13844;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____13852 = lift_c1 () in solve_eq uu____13852 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___133_13856  ->
                       match uu___133_13856 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____13857 -> false)) in
             let uu____13858 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____13882)::uu____13883,(wp2,uu____13885)::uu____13886)
                   -> (wp1, wp2)
               | uu____13927 ->
                   let uu____13940 =
                     let uu____13941 =
                       let uu____13944 =
                         let uu____13945 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____13946 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____13945 uu____13946 in
                       (uu____13944, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____13941 in
                   raise uu____13940 in
             match uu____13858 with
             | (wpc1,wpc2) ->
                 let uu____13963 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____13963
                 then
                   let uu____13966 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env uu____13966 wl
                 else
                   (let uu____13970 =
                      let uu____13974 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____13974 in
                    match uu____13970 with
                    | (c2_decl,qualifiers) ->
                        let uu____13986 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____13986
                        then
                          let c1_repr =
                            let uu____13989 =
                              let uu____13990 =
                                let uu____13991 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____13991 in
                              let uu____13992 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13990 uu____13992 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13989 in
                          let c2_repr =
                            let uu____13994 =
                              let uu____13995 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____13996 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13995 uu____13996 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13994 in
                          let prob =
                            let uu____13998 =
                              let uu____14001 =
                                let uu____14002 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____14003 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____14002
                                  uu____14003 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____14001 in
                            FStar_TypeChecker_Common.TProb uu____13998 in
                          let wl1 =
                            let uu____14005 =
                              let uu____14007 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives.fst in
                              Some uu____14007 in
                            solve_prob orig uu____14005 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____14014 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____14014
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____14016 =
                                     let uu____14019 =
                                       let uu____14020 =
                                         let uu____14030 =
                                           let uu____14031 =
                                             let uu____14032 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____14032] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____14031 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____14033 =
                                           let uu____14035 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____14036 =
                                             let uu____14038 =
                                               let uu____14039 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____14039 in
                                             [uu____14038] in
                                           uu____14035 :: uu____14036 in
                                         (uu____14030, uu____14033) in
                                       FStar_Syntax_Syntax.Tm_app uu____14020 in
                                     FStar_Syntax_Syntax.mk uu____14019 in
                                   uu____14016
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____14050 =
                                    let uu____14053 =
                                      let uu____14054 =
                                        let uu____14064 =
                                          let uu____14065 =
                                            let uu____14066 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____14066] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____14065 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____14067 =
                                          let uu____14069 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____14070 =
                                            let uu____14072 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____14073 =
                                              let uu____14075 =
                                                let uu____14076 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14076 in
                                              [uu____14075] in
                                            uu____14072 :: uu____14073 in
                                          uu____14069 :: uu____14070 in
                                        (uu____14064, uu____14067) in
                                      FStar_Syntax_Syntax.Tm_app uu____14054 in
                                    FStar_Syntax_Syntax.mk uu____14053 in
                                  uu____14050
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____14087 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_94  ->
                                  FStar_TypeChecker_Common.TProb _0_94)
                               uu____14087 in
                           let wl1 =
                             let uu____14093 =
                               let uu____14095 =
                                 let uu____14098 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____14098 g in
                               FStar_All.pipe_left (fun _0_95  -> Some _0_95)
                                 uu____14095 in
                             solve_prob orig uu____14093 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____14108 = FStar_Util.physical_equality c1 c2 in
        if uu____14108
        then
          let uu____14109 = solve_prob orig None [] wl in
          solve env uu____14109
        else
          ((let uu____14112 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____14112
            then
              let uu____14113 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____14114 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14113
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14114
            else ());
           (let uu____14116 =
              let uu____14119 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____14120 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____14119, uu____14120) in
            match uu____14116 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14124),FStar_Syntax_Syntax.Total
                    (t2,uu____14126)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14139 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14139 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14142,FStar_Syntax_Syntax.Total uu____14143) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14155),FStar_Syntax_Syntax.Total
                    (t2,uu____14157)) ->
                     let uu____14170 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14170 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14174),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14176)) ->
                     let uu____14189 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14189 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14193),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14195)) ->
                     let uu____14208 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14208 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14211,FStar_Syntax_Syntax.Comp uu____14212) ->
                     let uu____14218 =
                       let uu___177_14221 = problem in
                       let uu____14224 =
                         let uu____14225 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14225 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14221.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14224;
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14221.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___177_14221.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___177_14221.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14221.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14221.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14221.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14221.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14221.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14218 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14226,FStar_Syntax_Syntax.Comp uu____14227) ->
                     let uu____14233 =
                       let uu___177_14236 = problem in
                       let uu____14239 =
                         let uu____14240 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14240 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14236.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14239;
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14236.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___177_14236.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___177_14236.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14236.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14236.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14236.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14236.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14236.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14233 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14241,FStar_Syntax_Syntax.GTotal uu____14242) ->
                     let uu____14248 =
                       let uu___178_14251 = problem in
                       let uu____14254 =
                         let uu____14255 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14255 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14251.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___178_14251.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14251.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14254;
                         FStar_TypeChecker_Common.element =
                           (uu___178_14251.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14251.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14251.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14251.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14251.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14251.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14248 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14256,FStar_Syntax_Syntax.Total uu____14257) ->
                     let uu____14263 =
                       let uu___178_14266 = problem in
                       let uu____14269 =
                         let uu____14270 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14270 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14266.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___178_14266.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14266.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14269;
                         FStar_TypeChecker_Common.element =
                           (uu___178_14266.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14266.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14266.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14266.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14266.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14266.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14263 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14271,FStar_Syntax_Syntax.Comp uu____14272) ->
                     let uu____14273 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____14273
                     then
                       let uu____14274 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type" in
                       solve_t env uu____14274 wl
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
                           (let uu____14284 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____14284
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14286 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____14286 with
                            | None  ->
                                let uu____14288 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14289 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____14289) in
                                if uu____14288
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
                                  (let uu____14292 =
                                     let uu____14293 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____14294 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14293 uu____14294 in
                                   giveup env uu____14292 orig)
                            | Some edge -> solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14299 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14315  ->
              match uu____14315 with
              | (uu____14322,uu____14323,u,uu____14325,uu____14326,uu____14327)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____14299 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14345 =
        FStar_All.pipe_right (fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____14345 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____14355 =
        FStar_All.pipe_right (snd ineqs)
          (FStar_List.map
             (fun uu____14367  ->
                match uu____14367 with
                | (u1,u2) ->
                    let uu____14372 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____14373 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____14372 uu____14373)) in
      FStar_All.pipe_right uu____14355 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14385,[])) -> "{}"
      | uu____14398 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14408 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____14408
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____14411 =
              FStar_List.map
                (fun uu____14415  ->
                   match uu____14415 with
                   | (uu____14418,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____14411 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____14422 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14422 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14460 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____14460
    then
      let uu____14461 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____14462 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14461
        (rel_to_string rel) uu____14462
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
            let uu____14482 =
              let uu____14484 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_96  -> Some _0_96) uu____14484 in
            FStar_Syntax_Syntax.new_bv uu____14482 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____14490 =
              let uu____14492 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_97  -> Some _0_97) uu____14492 in
            let uu____14494 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____14490 uu____14494 in
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
          let uu____14517 = FStar_Options.eager_inference () in
          if uu____14517
          then
            let uu___179_14518 = probs in
            {
              attempting = (uu___179_14518.attempting);
              wl_deferred = (uu___179_14518.wl_deferred);
              ctr = (uu___179_14518.ctr);
              defer_ok = false;
              smt_ok = (uu___179_14518.smt_ok);
              tcenv = (uu___179_14518.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Syntax_Unionfind.rollback tx;
             (let uu____14529 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____14529
              then
                let uu____14530 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____14530
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
          ((let uu____14540 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____14540
            then
              let uu____14541 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14541
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____14545 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____14545
             then
               let uu____14546 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14546
             else ());
            (let f2 =
               let uu____14549 =
                 let uu____14550 = FStar_Syntax_Util.unmeta f1 in
                 uu____14550.FStar_Syntax_Syntax.n in
               match uu____14549 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14554 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___180_14555 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___180_14555.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___180_14555.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___180_14555.FStar_TypeChecker_Env.implicits)
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
            let uu____14570 =
              let uu____14571 =
                let uu____14572 =
                  let uu____14573 =
                    FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____14573
                    (fun _0_98  -> FStar_TypeChecker_Common.NonTrivial _0_98) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14572;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____14571 in
            FStar_All.pipe_left (fun _0_99  -> Some _0_99) uu____14570
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____14606 =
        let uu____14607 =
          let uu____14608 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
          FStar_All.pipe_right uu____14608
            (fun _0_100  -> FStar_TypeChecker_Common.NonTrivial _0_100) in
        {
          FStar_TypeChecker_Env.guard_f = uu____14607;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      Some uu____14606
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
          (let uu____14634 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14634
           then
             let uu____14635 = FStar_Syntax_Print.term_to_string t1 in
             let uu____14636 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14635
               uu____14636
           else ());
          (let prob =
             let uu____14639 =
               let uu____14642 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____14642 in
             FStar_All.pipe_left
               (fun _0_101  -> FStar_TypeChecker_Common.TProb _0_101)
               uu____14639 in
           let g =
             let uu____14647 =
               let uu____14649 = singleton' env prob smt_ok in
               solve_and_commit env uu____14649 (fun uu____14650  -> None) in
             FStar_All.pipe_left (with_guard env prob) uu____14647 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14664 = try_teq true env t1 t2 in
        match uu____14664 with
        | None  ->
            let uu____14666 =
              let uu____14667 =
                let uu____14670 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                let uu____14671 = FStar_TypeChecker_Env.get_range env in
                (uu____14670, uu____14671) in
              FStar_Errors.Error uu____14667 in
            raise uu____14666
        | Some g ->
            ((let uu____14674 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____14674
              then
                let uu____14675 = FStar_Syntax_Print.term_to_string t1 in
                let uu____14676 = FStar_Syntax_Print.term_to_string t2 in
                let uu____14677 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14675
                  uu____14676 uu____14677
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
          (let uu____14693 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14693
           then
             let uu____14694 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____14695 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14694
               uu____14695
           else ());
          (let uu____14697 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____14697 with
           | (prob,x) ->
               let g =
                 let uu____14705 =
                   let uu____14707 = singleton' env prob smt_ok in
                   solve_and_commit env uu____14707
                     (fun uu____14708  -> None) in
                 FStar_All.pipe_left (with_guard env prob) uu____14705 in
               ((let uu____14714 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____14714
                 then
                   let uu____14715 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____14716 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____14717 =
                     let uu____14718 = FStar_Util.must g in
                     guard_to_string env uu____14718 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14715 uu____14716 uu____14717
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
          let uu____14742 = FStar_TypeChecker_Env.get_range env in
          let uu____14743 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.err uu____14742 uu____14743
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____14755 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____14755
         then
           let uu____14756 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____14757 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____14756
             uu____14757
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____14762 =
             let uu____14765 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None uu____14765 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_102  -> FStar_TypeChecker_Common.CProb _0_102)
             uu____14762 in
         let uu____14768 =
           let uu____14770 = singleton env prob in
           solve_and_commit env uu____14770 (fun uu____14771  -> None) in
         FStar_All.pipe_left (with_guard env prob) uu____14768)
let solve_universe_inequalities':
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____14790  ->
        match uu____14790 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____14815 =
                 let uu____14816 =
                   let uu____14819 =
                     let uu____14820 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____14821 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____14820 uu____14821 in
                   let uu____14822 = FStar_TypeChecker_Env.get_range env in
                   (uu____14819, uu____14822) in
                 FStar_Errors.Error uu____14816 in
               raise uu____14815) in
            let equiv1 v1 v' =
              let uu____14830 =
                let uu____14833 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____14834 = FStar_Syntax_Subst.compress_univ v' in
                (uu____14833, uu____14834) in
              match uu____14830 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____14841 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____14855 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____14855 with
                      | FStar_Syntax_Syntax.U_unif uu____14859 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____14870  ->
                                    match uu____14870 with
                                    | (u,v') ->
                                        let uu____14876 = equiv1 v1 v' in
                                        if uu____14876
                                        then
                                          let uu____14878 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____14878 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____14888 -> [])) in
            let uu____14891 =
              let wl =
                let uu___181_14894 = empty_worklist env in
                {
                  attempting = (uu___181_14894.attempting);
                  wl_deferred = (uu___181_14894.wl_deferred);
                  ctr = (uu___181_14894.ctr);
                  defer_ok = false;
                  smt_ok = (uu___181_14894.smt_ok);
                  tcenv = (uu___181_14894.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____14901  ->
                      match uu____14901 with
                      | (lb,v1) ->
                          let uu____14906 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____14906 with
                           | USolved wl1 -> ()
                           | uu____14908 -> fail lb v1))) in
            let rec check_ineq uu____14914 =
              match uu____14914 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____14921) -> true
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
                      uu____14932,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____14934,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____14939) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____14943,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____14948 -> false) in
            let uu____14951 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____14957  ->
                      match uu____14957 with
                      | (u,v1) ->
                          let uu____14962 = check_ineq (u, v1) in
                          if uu____14962
                          then true
                          else
                            ((let uu____14965 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____14965
                              then
                                let uu____14966 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____14967 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____14966
                                  uu____14967
                              else ());
                             false))) in
            if uu____14951
            then ()
            else
              ((let uu____14971 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____14971
                then
                  ((let uu____14973 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____14973);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____14979 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____14979))
                else ());
               (let uu____14985 =
                  let uu____14986 =
                    let uu____14989 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____14989) in
                  FStar_Errors.Error uu____14986 in
                raise uu____14985))
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
      let fail uu____15022 =
        match uu____15022 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____15032 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____15032
       then
         let uu____15033 = wl_to_string wl in
         let uu____15034 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____15033 uu____15034
       else ());
      (let g1 =
         let uu____15049 = solve_and_commit env wl fail in
         match uu____15049 with
         | Some [] ->
             let uu___182_15056 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___182_15056.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___182_15056.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___182_15056.FStar_TypeChecker_Env.implicits)
             }
         | uu____15059 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___183_15062 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___183_15062.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___183_15062.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___183_15062.FStar_TypeChecker_Env.implicits)
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
            let uu___184_15088 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___184_15088.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___184_15088.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___184_15088.FStar_TypeChecker_Env.implicits)
            } in
          let uu____15089 =
            let uu____15090 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____15090 in
          if uu____15089
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15096 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____15096
                   then
                     let uu____15097 = FStar_TypeChecker_Env.get_range env in
                     let uu____15098 =
                       let uu____15099 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15099 in
                     FStar_Errors.diag uu____15097 uu____15098
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding] env vc in
                   let uu____15102 = check_trivial vc1 in
                   match uu____15102 with
                   | FStar_TypeChecker_Common.Trivial  -> Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then None
                       else
                         ((let uu____15109 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15109
                           then
                             let uu____15110 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____15111 =
                               let uu____15112 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15112 in
                             FStar_Errors.diag uu____15110 uu____15111
                           else ());
                          (let vcs =
                             let uu____15118 = FStar_Options.use_tactics () in
                             if uu____15118
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)] in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____15132  ->
                                   match uu____15132 with
                                   | (env1,goal) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify]
                                           env1 goal in
                                       let uu____15138 = check_trivial goal1 in
                                       (match uu____15138 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____15140 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____15140
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                                               ();
                                             (let uu____15145 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____15145
                                              then
                                                let uu____15146 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____15147 =
                                                  let uu____15148 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____15149 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____15148 uu____15149 in
                                                FStar_Errors.diag uu____15146
                                                  uu____15147
                                              else ());
                                             (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                               use_env_range_msg env1 goal2)))));
                          Some ret_g))))
let discharge_guard_no_smt:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15157 = discharge_guard' None env g false in
      match uu____15157 with
      | Some g1 -> g1
      | None  ->
          let uu____15162 =
            let uu____15163 =
              let uu____15166 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____15166) in
            FStar_Errors.Error uu____15163 in
          raise uu____15162
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15173 = discharge_guard' None env g true in
      match uu____15173 with
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
        let uu____15188 = FStar_Syntax_Unionfind.find u in
        match uu____15188 with | None  -> true | uu____15190 -> false in
      let rec until_fixpoint acc implicits =
        let uu____15203 = acc in
        match uu____15203 with
        | (out,changed) ->
            (match implicits with
             | [] ->
                 if Prims.op_Negation changed
                 then out
                 else until_fixpoint ([], false) out
             | hd1::tl1 ->
                 let uu____15249 = hd1 in
                 (match uu____15249 with
                  | (uu____15256,env,u,tm,k,r) ->
                      let uu____15262 = unresolved u in
                      if uu____15262
                      then until_fixpoint ((hd1 :: out), changed) tl1
                      else
                        (let env1 =
                           FStar_TypeChecker_Env.set_expected_typ env k in
                         let tm1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta] env1 tm in
                         (let uu____15280 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "RelCheck") in
                          if uu____15280
                          then
                            let uu____15281 =
                              FStar_Syntax_Print.uvar_to_string u in
                            let uu____15282 =
                              FStar_Syntax_Print.term_to_string tm1 in
                            let uu____15283 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print3
                              "Checking uvar %s resolved to %s at type %s\n"
                              uu____15281 uu____15282 uu____15283
                          else ());
                         (let env2 =
                            if forcelax
                            then
                              let uu___185_15286 = env1 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___185_15286.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___185_15286.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___185_15286.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___185_15286.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___185_15286.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___185_15286.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___185_15286.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___185_15286.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___185_15286.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___185_15286.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___185_15286.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___185_15286.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___185_15286.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___185_15286.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___185_15286.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___185_15286.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___185_15286.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___185_15286.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___185_15286.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___185_15286.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___185_15286.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___185_15286.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___185_15286.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___185_15286.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___185_15286.FStar_TypeChecker_Env.synth)
                              }
                            else env1 in
                          let uu____15288 =
                            env2.FStar_TypeChecker_Env.type_of
                              (let uu___186_15292 = env2 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___186_15292.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___186_15292.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___186_15292.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___186_15292.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___186_15292.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___186_15292.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___186_15292.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___186_15292.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___186_15292.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___186_15292.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___186_15292.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___186_15292.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___186_15292.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___186_15292.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___186_15292.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___186_15292.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___186_15292.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___186_15292.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___186_15292.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___186_15292.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___186_15292.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___186_15292.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___186_15292.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___186_15292.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___186_15292.FStar_TypeChecker_Env.synth)
                               }) tm1 in
                          match uu____15288 with
                          | (uu____15293,uu____15294,g1) ->
                              let g2 =
                                if env2.FStar_TypeChecker_Env.is_pattern
                                then
                                  let uu___187_15297 = g1 in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      FStar_TypeChecker_Common.Trivial;
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___187_15297.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___187_15297.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits =
                                      (uu___187_15297.FStar_TypeChecker_Env.implicits)
                                  }
                                else g1 in
                              let g' =
                                let uu____15300 =
                                  discharge_guard'
                                    (Some
                                       (fun uu____15304  ->
                                          FStar_Syntax_Print.term_to_string
                                            tm1)) env2 g2 true in
                                match uu____15300 with
                                | Some g3 -> g3
                                | None  ->
                                    failwith
                                      "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                              until_fixpoint
                                ((FStar_List.append
                                    g'.FStar_TypeChecker_Env.implicits out),
                                  true) tl1)))) in
      let uu___188_15319 = g in
      let uu____15320 =
        until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___188_15319.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___188_15319.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs =
          (uu___188_15319.FStar_TypeChecker_Env.univ_ineqs);
        FStar_TypeChecker_Env.implicits = uu____15320
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
        let uu____15354 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____15354 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15361 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15361
      | (reason,uu____15363,uu____15364,e,t,r)::uu____15368 ->
          let uu____15382 =
            let uu____15383 = FStar_Syntax_Print.term_to_string t in
            let uu____15384 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2
              "Failed to resolve implicit argument of type '%s' introduced in %s"
              uu____15383 uu____15384 in
          FStar_Errors.err r uu____15382
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___189_15391 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___189_15391.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___189_15391.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___189_15391.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15409 = try_teq false env t1 t2 in
        match uu____15409 with
        | None  -> false
        | Some g ->
            let uu____15412 = discharge_guard' None env g false in
            (match uu____15412 with
             | Some uu____15416 -> true
             | None  -> false)