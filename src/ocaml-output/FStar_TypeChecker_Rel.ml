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
type solution =
  | Success of FStar_TypeChecker_Common.deferred
  | Failed of (FStar_TypeChecker_Common.prob* Prims.string)
let uu___is_Success: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____520 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____534 -> false
let __proj__Failed__item___0:
  solution -> (FStar_TypeChecker_Common.prob* Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0
type variance =
  | COVARIANT
  | CONTRAVARIANT
  | INVARIANT
let uu___is_COVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____551 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____555 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____559 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___106_576  ->
    match uu___106_576 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____589 =
    let uu____590 = FStar_Syntax_Subst.compress t in
    uu____590.FStar_Syntax_Syntax.n in
  match uu____589 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____607 = FStar_Syntax_Print.uvar_to_string u in
      let uu____608 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____607 uu____608
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____611;
         FStar_Syntax_Syntax.pos = uu____612;
         FStar_Syntax_Syntax.vars = uu____613;_},args)
      ->
      let uu____641 = FStar_Syntax_Print.uvar_to_string u in
      let uu____642 = FStar_Syntax_Print.term_to_string ty in
      let uu____643 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" uu____641 uu____642 uu____643
  | uu____644 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___107_650  ->
      match uu___107_650 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____654 =
            let uu____656 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____657 =
              let uu____659 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____660 =
                let uu____662 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____663 =
                  let uu____665 =
                    let uu____667 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____668 =
                      let uu____670 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____671 =
                        let uu____673 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (fst p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____674 =
                          let uu____676 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____676] in
                        uu____673 :: uu____674 in
                      uu____670 :: uu____671 in
                    uu____667 :: uu____668 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____665 in
                uu____662 :: uu____663 in
              uu____659 :: uu____660 in
            uu____656 :: uu____657 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____654
      | FStar_TypeChecker_Common.CProb p ->
          let uu____681 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____682 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____681
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____682
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___108_688  ->
      match uu___108_688 with
      | UNIV (u,t) ->
          let x =
            let uu____692 = FStar_Options.hide_uvar_nums () in
            if uu____692
            then "?"
            else
              (let uu____694 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____694 FStar_Util.string_of_int) in
          let uu____695 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____695
      | TERM ((u,uu____697),t) ->
          let x =
            let uu____702 = FStar_Options.hide_uvar_nums () in
            if uu____702
            then "?"
            else
              (let uu____704 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____704 FStar_Util.string_of_int) in
          let uu____705 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____705
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____714 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____714 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____722 =
      let uu____724 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____724
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____722 (FStar_String.concat ", ")
let args_to_string args =
  let uu____742 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____750  ->
            match uu____750 with
            | (x,uu____754) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right uu____742 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____759 =
      let uu____760 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____760 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____759;
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
        let uu___139_773 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___139_773.wl_deferred);
          ctr = (uu___139_773.ctr);
          defer_ok = (uu___139_773.defer_ok);
          smt_ok;
          tcenv = (uu___139_773.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___140_798 = empty_worklist env in
  let uu____799 = FStar_List.map FStar_Pervasives.snd g in
  {
    attempting = uu____799;
    wl_deferred = (uu___140_798.wl_deferred);
    ctr = (uu___140_798.ctr);
    defer_ok = false;
    smt_ok = (uu___140_798.smt_ok);
    tcenv = (uu___140_798.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___141_811 = wl in
        {
          attempting = (uu___141_811.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___141_811.ctr);
          defer_ok = (uu___141_811.defer_ok);
          smt_ok = (uu___141_811.smt_ok);
          tcenv = (uu___141_811.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___142_823 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___142_823.wl_deferred);
        ctr = (uu___142_823.ctr);
        defer_ok = (uu___142_823.defer_ok);
        smt_ok = (uu___142_823.smt_ok);
        tcenv = (uu___142_823.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____834 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____834
         then
           let uu____835 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____835
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___109_839  ->
    match uu___109_839 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___143_855 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___143_855.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___143_855.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___143_855.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___143_855.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___143_855.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___143_855.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___143_855.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___110_876  ->
    match uu___110_876 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_43  -> FStar_TypeChecker_Common.CProb _0_43)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___111_892  ->
      match uu___111_892 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___112_895  ->
    match uu___112_895 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___113_904  ->
    match uu___113_904 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___114_914  ->
    match uu___114_914 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___115_924  ->
    match uu___115_924 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun uu___116_935  ->
    match uu___116_935 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___117_946  ->
    match uu___117_946 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___118_955  ->
    match uu___118_955 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.TProb _0_44) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_45  -> FStar_TypeChecker_Common.CProb _0_45) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____969 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____969 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____984  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1034 = next_pid () in
  let uu____1035 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1034;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1035;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1082 = next_pid () in
  let uu____1083 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1082;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1083;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1124 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1124;
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
        let uu____1176 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1176
        then
          let uu____1177 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1178 = prob_to_string env d in
          let uu____1179 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1177 uu____1178 uu____1179 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1184 -> failwith "impossible" in
           let uu____1185 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1193 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1194 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1193, uu____1194)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1198 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1199 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1198, uu____1199) in
           match uu____1185 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___119_1208  ->
            match uu___119_1208 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1214 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1216),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___120_1229  ->
           match uu___120_1229 with
           | UNIV uu____1231 -> None
           | TERM ((u,uu____1235),t) ->
               let uu____1239 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1239 then Some t else None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___121_1251  ->
           match uu___121_1251 with
           | UNIV (u',t) ->
               let uu____1255 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1255 then Some t else None
           | uu____1258 -> None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1265 =
        let uu____1266 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1266 in
      FStar_Syntax_Subst.compress uu____1265
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1273 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1273
let norm_arg env t = let uu____1292 = sn env (fst t) in (uu____1292, (snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1309  ->
              match uu____1309 with
              | (x,imp) ->
                  let uu____1316 =
                    let uu___144_1317 = x in
                    let uu____1318 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___144_1317.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___144_1317.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1318
                    } in
                  (uu____1316, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1333 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1333
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1336 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1336
        | uu____1338 -> u2 in
      let uu____1339 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1339
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1446 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____1446 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1458;
               FStar_Syntax_Syntax.pos = uu____1459;
               FStar_Syntax_Syntax.vars = uu____1460;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1481 =
                 let uu____1482 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1483 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1482
                   uu____1483 in
               failwith uu____1481)
    | FStar_Syntax_Syntax.Tm_uinst uu____1493 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1520 =
             let uu____1521 = FStar_Syntax_Subst.compress t1' in
             uu____1521.FStar_Syntax_Syntax.n in
           match uu____1520 with
           | FStar_Syntax_Syntax.Tm_refine uu____1533 -> aux true t1'
           | uu____1538 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1550 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1573 =
             let uu____1574 = FStar_Syntax_Subst.compress t1' in
             uu____1574.FStar_Syntax_Syntax.n in
           match uu____1573 with
           | FStar_Syntax_Syntax.Tm_refine uu____1586 -> aux true t1'
           | uu____1591 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_app uu____1603 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1635 =
             let uu____1636 = FStar_Syntax_Subst.compress t1' in
             uu____1636.FStar_Syntax_Syntax.n in
           match uu____1635 with
           | FStar_Syntax_Syntax.Tm_refine uu____1648 -> aux true t1'
           | uu____1653 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_type uu____1665 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_constant uu____1677 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_name uu____1689 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1701 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1713 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_abs uu____1732 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1758 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_let uu____1778 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_match uu____1797 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_meta uu____1824 ->
        let uu____1829 =
          let uu____1830 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1831 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1830
            uu____1831 in
        failwith uu____1829
    | FStar_Syntax_Syntax.Tm_ascribed uu____1841 ->
        let uu____1859 =
          let uu____1860 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1861 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1860
            uu____1861 in
        failwith uu____1859
    | FStar_Syntax_Syntax.Tm_delayed uu____1871 ->
        let uu____1892 =
          let uu____1893 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1894 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1893
            uu____1894 in
        failwith uu____1892
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1904 =
          let uu____1905 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1906 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1905
            uu____1906 in
        failwith uu____1904 in
  let uu____1916 = whnf env t1 in aux false uu____1916
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1925 =
        let uu____1935 = empty_worklist env in
        base_and_refinement env uu____1935 t in
      FStar_All.pipe_right uu____1925 FStar_Pervasives.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____1959 = FStar_Syntax_Syntax.null_bv t in
    (uu____1959, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____1979 = base_and_refinement env wl t in
  match uu____1979 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
let force_refinement uu____2038 =
  match uu____2038 with
  | (t_base,refopt) ->
      let uu____2052 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base in
      (match uu____2052 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___122_2076  ->
      match uu___122_2076 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2080 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2081 =
            let uu____2082 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____2082 in
          let uu____2083 =
            let uu____2084 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____2084 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2080 uu____2081
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2083
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2088 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2089 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____2090 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2088 uu____2089
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2090
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2094 =
      let uu____2096 =
        let uu____2098 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2108  ->
                  match uu____2108 with | (uu____2112,uu____2113,x) -> x)) in
        FStar_List.append wl.attempting uu____2098 in
      FStar_List.map (wl_prob_to_string wl) uu____2096 in
    FStar_All.pipe_right uu____2094 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2131 =
          let uu____2141 =
            let uu____2142 = FStar_Syntax_Subst.compress k in
            uu____2142.FStar_Syntax_Syntax.n in
          match uu____2141 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2187 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2187)
              else
                (let uu____2201 = FStar_Syntax_Util.abs_formals t in
                 match uu____2201 with
                 | (ys',t1,uu____2222) ->
                     let uu____2235 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2235))
          | uu____2256 ->
              let uu____2257 =
                let uu____2263 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____2263) in
              ((ys, t), uu____2257) in
        match uu____2131 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2322 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2322 c in
               let uu____2324 =
                 let uu____2331 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_46  -> FStar_Util.Inl _0_46) in
                 FStar_All.pipe_right uu____2331 (fun _0_47  -> Some _0_47) in
               FStar_Syntax_Util.abs ys1 t1 uu____2324)
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
            let uu____2382 = p_guard prob in
            match uu____2382 with
            | (uu____2385,uv) ->
                ((let uu____2388 =
                    let uu____2389 = FStar_Syntax_Subst.compress uv in
                    uu____2389.FStar_Syntax_Syntax.n in
                  match uu____2388 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2409 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2409
                        then
                          let uu____2410 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2411 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2412 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2410
                            uu____2411 uu____2412
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2414 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___145_2417 = wl in
                  {
                    attempting = (uu___145_2417.attempting);
                    wl_deferred = (uu___145_2417.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___145_2417.defer_ok);
                    smt_ok = (uu___145_2417.smt_ok);
                    tcenv = (uu___145_2417.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2430 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2430
         then
           let uu____2431 = FStar_Util.string_of_int pid in
           let uu____2432 =
             let uu____2433 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2433 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2431 uu____2432
         else ());
        commit sol;
        (let uu___146_2438 = wl in
         {
           attempting = (uu___146_2438.attempting);
           wl_deferred = (uu___146_2438.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___146_2438.defer_ok);
           smt_ok = (uu___146_2438.smt_ok);
           tcenv = (uu___146_2438.tcenv)
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
            | (uu____2467,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2475 = FStar_Syntax_Util.mk_conj t1 f in
                Some uu____2475 in
          (let uu____2481 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2481
           then
             let uu____2482 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2483 =
               let uu____2484 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2484 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2482 uu____2483
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2509 =
    let uu____2513 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2513 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2509
    (FStar_Util.for_some
       (fun uu____2530  ->
          match uu____2530 with
          | (uv,uu____2534) -> FStar_Syntax_Unionfind.equiv uv (fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2567 = occurs wl uk t in Prims.op_Negation uu____2567 in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2572 =
         let uu____2573 = FStar_Syntax_Print.uvar_to_string (fst uk) in
         let uu____2574 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2573 uu____2574 in
       Some uu____2572) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2622 = occurs_check env wl uk t in
  match uu____2622 with
  | (occurs_ok,msg) ->
      let uu____2639 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2639, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2703 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2727  ->
            fun uu____2728  ->
              match (uu____2727, uu____2728) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2771 =
                    let uu____2772 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2772 in
                  if uu____2771
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2786 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2786
                     then
                       let uu____2793 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____2793)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2703 with | (isect,uu____2815) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2868  ->
          fun uu____2869  ->
            match (uu____2868, uu____2869) with
            | ((a,uu____2879),(b,uu____2881)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2925 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2931  ->
                match uu____2931 with
                | (b,uu____2935) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____2925 then None else Some (a, (snd hd1))
  | uu____2944 -> None
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
            let uu____2987 = pat_var_opt env seen hd1 in
            (match uu____2987 with
             | None  ->
                 ((let uu____2995 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____2995
                   then
                     let uu____2996 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____2996
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3008 =
      let uu____3009 = FStar_Syntax_Subst.compress t in
      uu____3009.FStar_Syntax_Syntax.n in
    match uu____3008 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3012 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3021;
           FStar_Syntax_Syntax.tk = uu____3022;
           FStar_Syntax_Syntax.pos = uu____3023;
           FStar_Syntax_Syntax.vars = uu____3024;_},uu____3025)
        -> true
    | uu____3048 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3110;
         FStar_Syntax_Syntax.pos = uu____3111;
         FStar_Syntax_Syntax.vars = uu____3112;_},args)
      -> (t, uv, k, args)
  | uu____3153 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____3207 = destruct_flex_t t in
  match uu____3207 with
  | (t1,uv,k,args) ->
      let uu____3275 = pat_vars env [] args in
      (match uu____3275 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3331 -> ((t1, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth option*
  FStar_Syntax_Syntax.delta_depth option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3380 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth option* FStar_Syntax_Syntax.delta_depth
      option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3403 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3407 -> false
let head_match: match_result -> match_result =
  fun uu___123_3410  ->
    match uu___123_3410 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3419 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3432 ->
          let uu____3433 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3433 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3443 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3457 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3463 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> None
      | FStar_Syntax_Syntax.Tm_bvar uu____3485 -> None
      | FStar_Syntax_Syntax.Tm_name uu____3486 -> None
      | FStar_Syntax_Syntax.Tm_uvar uu____3487 -> None
      | FStar_Syntax_Syntax.Tm_let uu____3496 -> None
      | FStar_Syntax_Syntax.Tm_match uu____3504 -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3521) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3527,uu____3528) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3558) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3573;
             FStar_Syntax_Syntax.index = uu____3574;
             FStar_Syntax_Syntax.sort = t2;_},uu____3576)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3583 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3584 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3585 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3593 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3609 = fv_delta_depth env fv in Some uu____3609
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
            let uu____3628 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3628
            then FullMatch
            else
              (let uu____3630 =
                 let uu____3635 =
                   let uu____3637 = fv_delta_depth env f in Some uu____3637 in
                 let uu____3638 =
                   let uu____3640 = fv_delta_depth env g in Some uu____3640 in
                 (uu____3635, uu____3638) in
               MisMatch uu____3630)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3644),FStar_Syntax_Syntax.Tm_uinst (g,uu____3646)) ->
            let uu____3655 = head_matches env f g in
            FStar_All.pipe_right uu____3655 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3662),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3664)) ->
            let uu____3689 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____3689 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3694),FStar_Syntax_Syntax.Tm_refine (y,uu____3696)) ->
            let uu____3705 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3705 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3707),uu____3708) ->
            let uu____3713 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3713 head_match
        | (uu____3714,FStar_Syntax_Syntax.Tm_refine (x,uu____3716)) ->
            let uu____3721 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3721 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3722,FStar_Syntax_Syntax.Tm_type
           uu____3723) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3724,FStar_Syntax_Syntax.Tm_arrow uu____3725) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3741),FStar_Syntax_Syntax.Tm_app (head',uu____3743))
            ->
            let uu____3772 = head_matches env head1 head' in
            FStar_All.pipe_right uu____3772 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3774),uu____3775) ->
            let uu____3790 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____3790 head_match
        | (uu____3791,FStar_Syntax_Syntax.Tm_app (head1,uu____3793)) ->
            let uu____3808 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____3808 head_match
        | uu____3809 ->
            let uu____3812 =
              let uu____3817 = delta_depth_of_term env t11 in
              let uu____3819 = delta_depth_of_term env t21 in
              (uu____3817, uu____3819) in
            MisMatch uu____3812
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3855 = FStar_Syntax_Util.head_and_args t in
    match uu____3855 with
    | (head1,uu____3867) ->
        let uu____3882 =
          let uu____3883 = FStar_Syntax_Util.un_uinst head1 in
          uu____3883.FStar_Syntax_Syntax.n in
        (match uu____3882 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3888 =
               let uu____3889 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____3889 FStar_Option.isSome in
             if uu____3888
             then
               let uu____3903 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____3903 (fun _0_48  -> Some _0_48)
             else None
         | uu____3906 -> None) in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None)) in
  let fail r = (r, None) in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21 in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),uu____3974) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____3984 =
             let uu____3989 = maybe_inline t11 in
             let uu____3991 = maybe_inline t21 in (uu____3989, uu____3991) in
           match uu____3984 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (uu____4012,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4022 =
             let uu____4027 = maybe_inline t11 in
             let uu____4029 = maybe_inline t21 in (uu____4027, uu____4029) in
           match uu____4022 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____4054 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____4054 with
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
        let uu____4069 =
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
             let uu____4077 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____4077)) in
        (match uu____4069 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4085 -> fail r
    | uu____4090 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4119 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4149 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4164 = FStar_Syntax_Util.type_u () in
      match uu____4164 with
      | (t,uu____4168) ->
          let uu____4169 = new_uvar r binders t in fst uu____4169
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4178 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____4178 FStar_Pervasives.fst
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
        let uu____4220 = head_matches env t1 t' in
        match uu____4220 with
        | MisMatch uu____4221 -> false
        | uu____4226 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4286,imp),T (t2,uu____4289)) -> (t2, imp)
                     | uu____4306 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4346  ->
                    match uu____4346 with
                    | (t2,uu____4354) ->
                        (None, INVARIANT, (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____4384 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____4384 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4437))::tcs2) ->
                       aux
                         (((let uu___147_4459 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___147_4459.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___147_4459.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4469 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___124_4500 =
                 match uu___124_4500 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4563 = decompose1 [] bs1 in
               (rebuild, matches, uu____4563))
      | uu____4591 ->
          let rebuild uu___125_4596 =
            match uu___125_4596 with
            | [] -> t1
            | uu____4598 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___126_4617  ->
    match uu___126_4617 with
    | T (t,uu____4619) -> t
    | uu____4628 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___127_4631  ->
    match uu___127_4631 with
    | T (t,uu____4633) -> FStar_Syntax_Syntax.as_arg t
    | uu____4642 -> failwith "Impossible"
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
              | (uu____4711,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4730 = new_uvar r scope1 k in
                  (match uu____4730 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4742 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args)) None r in
                       let uu____4757 =
                         let uu____4758 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_49  ->
                              FStar_TypeChecker_Common.TProb _0_49)
                           uu____4758 in
                       ((T (gi_xs, mk_kind)), uu____4757))
              | (uu____4767,uu____4768,C uu____4769) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4856 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4867;
                         FStar_Syntax_Syntax.pos = uu____4868;
                         FStar_Syntax_Syntax.vars = uu____4869;_})
                        ->
                        let uu____4884 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4884 with
                         | (T (gi_xs,uu____4900),prob) ->
                             let uu____4910 =
                               let uu____4911 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_50  -> C _0_50)
                                 uu____4911 in
                             (uu____4910, [prob])
                         | uu____4913 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4923;
                         FStar_Syntax_Syntax.pos = uu____4924;
                         FStar_Syntax_Syntax.vars = uu____4925;_})
                        ->
                        let uu____4940 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4940 with
                         | (T (gi_xs,uu____4956),prob) ->
                             let uu____4966 =
                               let uu____4967 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_51  -> C _0_51)
                                 uu____4967 in
                             (uu____4966, [prob])
                         | uu____4969 -> failwith "impossible")
                    | (uu____4975,uu____4976,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____4978;
                         FStar_Syntax_Syntax.pos = uu____4979;
                         FStar_Syntax_Syntax.vars = uu____4980;_})
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
                        let uu____5054 =
                          let uu____5059 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____5059 FStar_List.unzip in
                        (match uu____5054 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5088 =
                                 let uu____5089 =
                                   let uu____5092 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____5092 un_T in
                                 let uu____5093 =
                                   let uu____5099 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____5099
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5089;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5093;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5088 in
                             ((C gi_xs), sub_probs))
                    | uu____5104 ->
                        let uu____5111 = sub_prob scope1 args q in
                        (match uu____5111 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____4856 with
                   | (tc,probs) ->
                       let uu____5129 =
                         match q with
                         | (Some b,uu____5155,uu____5156) ->
                             let uu____5164 =
                               let uu____5168 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____5168 :: args in
                             ((Some b), (b :: scope1), uu____5164)
                         | uu____5186 -> (None, scope1, args) in
                       (match uu____5129 with
                        | (bopt,scope2,args1) ->
                            let uu____5229 = aux scope2 args1 qs2 in
                            (match uu____5229 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____5250 =
                                         let uu____5252 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         f :: uu____5252 in
                                       FStar_Syntax_Util.mk_conj_l uu____5250
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (fst b).FStar_Syntax_Syntax.sort in
                                       let uu____5265 =
                                         let uu____5267 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (fst b) f in
                                         let uu____5268 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         uu____5267 :: uu____5268 in
                                       FStar_Syntax_Util.mk_conj_l uu____5265 in
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
  let uu___148_5321 = p in
  let uu____5324 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____5325 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___148_5321.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5324;
    FStar_TypeChecker_Common.relation =
      (uu___148_5321.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5325;
    FStar_TypeChecker_Common.element =
      (uu___148_5321.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___148_5321.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___148_5321.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___148_5321.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___148_5321.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___148_5321.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5335 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____5335
            (fun _0_52  -> FStar_TypeChecker_Common.TProb _0_52)
      | FStar_TypeChecker_Common.CProb uu____5340 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5354 = compress_prob wl pr in
        FStar_All.pipe_right uu____5354 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5360 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____5360 with
           | (lh,uu____5373) ->
               let uu____5388 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____5388 with
                | (rh,uu____5401) ->
                    let uu____5416 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5425,FStar_Syntax_Syntax.Tm_uvar uu____5426)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5445,uu____5446)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5457,FStar_Syntax_Syntax.Tm_uvar uu____5458)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5469,uu____5470)
                          ->
                          let uu____5479 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5479 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5519 ->
                                    let rank =
                                      let uu____5526 = is_top_level_prob prob in
                                      if uu____5526
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5528 =
                                      let uu___149_5531 = tp in
                                      let uu____5534 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_5531.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___149_5531.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_5531.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5534;
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_5531.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_5531.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_5531.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_5531.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_5531.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_5531.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5528)))
                      | (uu____5544,FStar_Syntax_Syntax.Tm_uvar uu____5545)
                          ->
                          let uu____5554 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5554 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5594 ->
                                    let uu____5600 =
                                      let uu___150_5605 = tp in
                                      let uu____5608 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___150_5605.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5608;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___150_5605.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___150_5605.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___150_5605.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___150_5605.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___150_5605.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___150_5605.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___150_5605.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___150_5605.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5600)))
                      | (uu____5624,uu____5625) -> (rigid_rigid, tp) in
                    (match uu____5416 with
                     | (rank,tp1) ->
                         let uu____5636 =
                           FStar_All.pipe_right
                             (let uu___151_5639 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___151_5639.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___151_5639.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___151_5639.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___151_5639.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___151_5639.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___151_5639.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___151_5639.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___151_5639.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___151_5639.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_53  ->
                                FStar_TypeChecker_Common.TProb _0_53) in
                         (rank, uu____5636))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5645 =
            FStar_All.pipe_right
              (let uu___152_5648 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___152_5648.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___152_5648.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___152_5648.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___152_5648.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___152_5648.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___152_5648.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___152_5648.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___152_5648.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___152_5648.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_54  -> FStar_TypeChecker_Common.CProb _0_54) in
          (rigid_rigid, uu____5645)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob option* FStar_TypeChecker_Common.prob
      Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____5680 probs =
      match uu____5680 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5710 = rank wl hd1 in
               (match uu____5710 with
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
    match projectee with | UDeferred _0 -> true | uu____5778 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5790 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5802 -> false
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
                        let uu____5835 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____5835 with
                        | (k,uu____5839) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____5843 -> false)))
            | uu____5844 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____5891 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____5891 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5894 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____5900 =
                     let uu____5901 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____5902 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5901
                       uu____5902 in
                   UFailed uu____5900)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5918 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5918 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5936 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5936 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____5939 ->
                let uu____5942 =
                  let uu____5943 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____5944 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5943
                    uu____5944 msg in
                UFailed uu____5942 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____5945,uu____5946) ->
              let uu____5947 =
                let uu____5948 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5949 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5948 uu____5949 in
              failwith uu____5947
          | (FStar_Syntax_Syntax.U_unknown ,uu____5950) ->
              let uu____5951 =
                let uu____5952 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5953 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5952 uu____5953 in
              failwith uu____5951
          | (uu____5954,FStar_Syntax_Syntax.U_bvar uu____5955) ->
              let uu____5956 =
                let uu____5957 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5958 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5957 uu____5958 in
              failwith uu____5956
          | (uu____5959,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____5960 =
                let uu____5961 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5962 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5961 uu____5962 in
              failwith uu____5960
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____5974 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____5974
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____5984 = occurs_univ v1 u3 in
              if uu____5984
              then
                let uu____5985 =
                  let uu____5986 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____5987 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5986 uu____5987 in
                try_umax_components u11 u21 uu____5985
              else
                (let uu____5989 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____5989)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____5997 = occurs_univ v1 u3 in
              if uu____5997
              then
                let uu____5998 =
                  let uu____5999 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6000 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5999 uu____6000 in
                try_umax_components u11 u21 uu____5998
              else
                (let uu____6002 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6002)
          | (FStar_Syntax_Syntax.U_max uu____6005,uu____6006) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6011 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6011
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____6013,FStar_Syntax_Syntax.U_max uu____6014) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6019 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6019
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6021,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6022,FStar_Syntax_Syntax.U_name
             uu____6023) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6024) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6025) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6026,FStar_Syntax_Syntax.U_succ
             uu____6027) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6028,FStar_Syntax_Syntax.U_zero
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
  let uu____6090 = bc1 in
  match uu____6090 with
  | (bs1,mk_cod1) ->
      let uu____6115 = bc2 in
      (match uu____6115 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6162 = FStar_Util.first_N n1 bs in
             match uu____6162 with
             | (bs3,rest) ->
                 let uu____6176 = mk_cod rest in (bs3, uu____6176) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____6200 =
               let uu____6204 = mk_cod1 [] in (bs1, uu____6204) in
             let uu____6206 =
               let uu____6210 = mk_cod2 [] in (bs2, uu____6210) in
             (uu____6200, uu____6206)
           else
             if l1 > l2
             then
               (let uu____6237 = curry l2 bs1 mk_cod1 in
                let uu____6247 =
                  let uu____6251 = mk_cod2 [] in (bs2, uu____6251) in
                (uu____6237, uu____6247))
             else
               (let uu____6260 =
                  let uu____6264 = mk_cod1 [] in (bs1, uu____6264) in
                let uu____6266 = curry l1 bs2 mk_cod2 in
                (uu____6260, uu____6266)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6373 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____6373
       then
         let uu____6374 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6374
       else ());
      (let uu____6376 = next_prob probs in
       match uu____6376 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___153_6389 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___153_6389.wl_deferred);
               ctr = (uu___153_6389.ctr);
               defer_ok = (uu___153_6389.defer_ok);
               smt_ok = (uu___153_6389.smt_ok);
               tcenv = (uu___153_6389.tcenv)
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
                  let uu____6396 = solve_flex_rigid_join env tp probs1 in
                  (match uu____6396 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6400 = solve_rigid_flex_meet env tp probs1 in
                     match uu____6400 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____6404,uu____6405) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6414 ->
                let uu____6419 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6447  ->
                          match uu____6447 with
                          | (c,uu____6452,uu____6453) -> c < probs.ctr)) in
                (match uu____6419 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6475 =
                            FStar_List.map
                              (fun uu____6481  ->
                                 match uu____6481 with
                                 | (uu____6487,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____6475
                      | uu____6490 ->
                          let uu____6495 =
                            let uu___154_6496 = probs in
                            let uu____6497 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6506  ->
                                      match uu____6506 with
                                      | (uu____6510,uu____6511,y) -> y)) in
                            {
                              attempting = uu____6497;
                              wl_deferred = rest;
                              ctr = (uu___154_6496.ctr);
                              defer_ok = (uu___154_6496.defer_ok);
                              smt_ok = (uu___154_6496.smt_ok);
                              tcenv = (uu___154_6496.tcenv)
                            } in
                          solve env uu____6495))))
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
            let uu____6518 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____6518 with
            | USolved wl1 ->
                let uu____6520 = solve_prob orig None [] wl1 in
                solve env uu____6520
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
                  let uu____6554 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6554 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6557 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6565;
                  FStar_Syntax_Syntax.pos = uu____6566;
                  FStar_Syntax_Syntax.vars = uu____6567;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6570;
                  FStar_Syntax_Syntax.pos = uu____6571;
                  FStar_Syntax_Syntax.vars = uu____6572;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6584,uu____6585) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6590,FStar_Syntax_Syntax.Tm_uinst uu____6591) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6596 -> USolved wl
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
            ((let uu____6604 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6604
              then
                let uu____6605 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6605 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6613 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6613
         then
           let uu____6614 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6614
         else ());
        (let uu____6616 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6616 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6658 = head_matches_delta env () t1 t2 in
               match uu____6658 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6680 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6706 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6715 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____6716 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____6715, uu____6716)
                          | None  ->
                              let uu____6719 = FStar_Syntax_Subst.compress t1 in
                              let uu____6720 = FStar_Syntax_Subst.compress t2 in
                              (uu____6719, uu____6720) in
                        (match uu____6706 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6742 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_55  ->
                                    FStar_TypeChecker_Common.TProb _0_55)
                                 uu____6742 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6765 =
                                    let uu____6771 =
                                      let uu____6774 =
                                        let uu____6777 =
                                          let uu____6778 =
                                            let uu____6783 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____6783) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6778 in
                                        FStar_Syntax_Syntax.mk uu____6777 in
                                      uu____6774 None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____6796 =
                                      let uu____6798 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____6798] in
                                    (uu____6771, uu____6796) in
                                  Some uu____6765
                              | (uu____6807,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6809)) ->
                                  let uu____6814 =
                                    let uu____6818 =
                                      let uu____6820 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____6820] in
                                    (t11, uu____6818) in
                                  Some uu____6814
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6826),uu____6827) ->
                                  let uu____6832 =
                                    let uu____6836 =
                                      let uu____6838 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____6838] in
                                    (t21, uu____6836) in
                                  Some uu____6832
                              | uu____6843 ->
                                  let uu____6846 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____6846 with
                                   | (head1,uu____6861) ->
                                       let uu____6876 =
                                         let uu____6877 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____6877.FStar_Syntax_Syntax.n in
                                       (match uu____6876 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6884;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6886;_}
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
                                        | uu____6895 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6904) ->
                  let uu____6917 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___128_6926  ->
                            match uu___128_6926 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6931 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____6931 with
                                      | (u',uu____6942) ->
                                          let uu____6957 =
                                            let uu____6958 = whnf env u' in
                                            uu____6958.FStar_Syntax_Syntax.n in
                                          (match uu____6957 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____6962) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____6975 -> false))
                                 | uu____6976 -> false)
                            | uu____6978 -> false)) in
                  (match uu____6917 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____6999 tps =
                         match uu____6999 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7026 =
                                    let uu____7031 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____7031 in
                                  (match uu____7026 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____7050 -> None) in
                       let uu____7055 =
                         let uu____7060 =
                           let uu____7064 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____7064, []) in
                         make_lower_bound uu____7060 lower_bounds in
                       (match uu____7055 with
                        | None  ->
                            ((let uu____7071 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7071
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
                            ((let uu____7084 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7084
                              then
                                let wl' =
                                  let uu___155_7086 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___155_7086.wl_deferred);
                                    ctr = (uu___155_7086.ctr);
                                    defer_ok = (uu___155_7086.defer_ok);
                                    smt_ok = (uu___155_7086.smt_ok);
                                    tcenv = (uu___155_7086.tcenv)
                                  } in
                                let uu____7087 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7087
                              else ());
                             (let uu____7089 =
                                solve_t env eq_prob
                                  (let uu___156_7090 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___156_7090.wl_deferred);
                                     ctr = (uu___156_7090.ctr);
                                     defer_ok = (uu___156_7090.defer_ok);
                                     smt_ok = (uu___156_7090.smt_ok);
                                     tcenv = (uu___156_7090.tcenv)
                                   }) in
                              match uu____7089 with
                              | Success uu____7092 ->
                                  let wl1 =
                                    let uu___157_7094 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___157_7094.wl_deferred);
                                      ctr = (uu___157_7094.ctr);
                                      defer_ok = (uu___157_7094.defer_ok);
                                      smt_ok = (uu___157_7094.smt_ok);
                                      tcenv = (uu___157_7094.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1 in
                                  let uu____7096 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds in
                                  Some wl2
                              | uu____7099 -> None))))
              | uu____7100 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7107 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____7107
         then
           let uu____7108 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7108
         else ());
        (let uu____7110 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____7110 with
         | (u,args) ->
             let uu____7137 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____7137 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____7168 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____7168 with
                    | (h1,args1) ->
                        let uu____7196 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____7196 with
                         | (h2,uu____7209) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7228 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____7228
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7243 =
                                          let uu____7245 =
                                            let uu____7246 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_56  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_56) uu____7246 in
                                          [uu____7245] in
                                        Some uu____7243))
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
                                       (let uu____7270 =
                                          let uu____7272 =
                                            let uu____7273 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_57  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_57) uu____7273 in
                                          [uu____7272] in
                                        Some uu____7270))
                                  else None
                              | uu____7281 -> None)) in
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
                             let uu____7347 =
                               let uu____7353 =
                                 let uu____7356 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____7356 in
                               (uu____7353, m1) in
                             Some uu____7347)
                    | (uu____7365,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7367)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7399),uu____7400) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____7431 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7465) ->
                       let uu____7478 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___129_7487  ->
                                 match uu___129_7487 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____7492 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____7492 with
                                           | (u',uu____7503) ->
                                               let uu____7518 =
                                                 let uu____7519 = whnf env u' in
                                                 uu____7519.FStar_Syntax_Syntax.n in
                                               (match uu____7518 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7523) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____7536 -> false))
                                      | uu____7537 -> false)
                                 | uu____7539 -> false)) in
                       (match uu____7478 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7564 tps =
                              match uu____7564 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7605 =
                                         let uu____7612 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7612 in
                                       (match uu____7605 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7647 -> None) in
                            let uu____7654 =
                              let uu____7661 =
                                let uu____7667 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7667, []) in
                              make_upper_bound uu____7661 upper_bounds in
                            (match uu____7654 with
                             | None  ->
                                 ((let uu____7676 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7676
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
                                 ((let uu____7695 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7695
                                   then
                                     let wl' =
                                       let uu___158_7697 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___158_7697.wl_deferred);
                                         ctr = (uu___158_7697.ctr);
                                         defer_ok = (uu___158_7697.defer_ok);
                                         smt_ok = (uu___158_7697.smt_ok);
                                         tcenv = (uu___158_7697.tcenv)
                                       } in
                                     let uu____7698 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7698
                                   else ());
                                  (let uu____7700 =
                                     solve_t env eq_prob
                                       (let uu___159_7701 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___159_7701.wl_deferred);
                                          ctr = (uu___159_7701.ctr);
                                          defer_ok = (uu___159_7701.defer_ok);
                                          smt_ok = (uu___159_7701.smt_ok);
                                          tcenv = (uu___159_7701.tcenv)
                                        }) in
                                   match uu____7700 with
                                   | Success uu____7703 ->
                                       let wl1 =
                                         let uu___160_7705 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___160_7705.wl_deferred);
                                           ctr = (uu___160_7705.ctr);
                                           defer_ok =
                                             (uu___160_7705.defer_ok);
                                           smt_ok = (uu___160_7705.smt_ok);
                                           tcenv = (uu___160_7705.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1 in
                                       let uu____7707 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds in
                                       Some wl2
                                   | uu____7710 -> None))))
                   | uu____7711 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____7776 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____7776
                      then
                        let uu____7777 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7777
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___161_7809 = hd1 in
                      let uu____7810 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_7809.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_7809.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7810
                      } in
                    let hd21 =
                      let uu___162_7814 = hd2 in
                      let uu____7815 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___162_7814.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___162_7814.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7815
                      } in
                    let prob =
                      let uu____7819 =
                        let uu____7822 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7822 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_58  -> FStar_TypeChecker_Common.TProb _0_58)
                        uu____7819 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____7830 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7830 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____7833 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____7833 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7851 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives.fst in
                           let uu____7854 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____7851 uu____7854 in
                         ((let uu____7860 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____7860
                           then
                             let uu____7861 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____7862 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7861 uu____7862
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7877 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____7883 = aux scope env [] bs1 bs2 in
              match uu____7883 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7899 = compress_tprob wl problem in
        solve_t' env uu____7899 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7932 = head_matches_delta env1 wl1 t1 t2 in
          match uu____7932 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7949,uu____7950) ->
                   let may_relate head3 =
                     let uu____7965 =
                       let uu____7966 = FStar_Syntax_Util.un_uinst head3 in
                       uu____7966.FStar_Syntax_Syntax.n in
                     match uu____7965 with
                     | FStar_Syntax_Syntax.Tm_name uu____7969 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____7970 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____7987 -> false in
                   let uu____7988 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____7988
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
                                let uu____8005 =
                                  let uu____8006 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____8006 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____8005 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____8008 = solve_prob orig (Some guard) [] wl1 in
                     solve env1 uu____8008
                   else
                     (let uu____8010 =
                        let uu____8011 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____8012 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____8011 uu____8012 in
                      giveup env1 uu____8010 orig)
               | (uu____8013,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___163_8021 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___163_8021.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___163_8021.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___163_8021.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___163_8021.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___163_8021.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___163_8021.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___163_8021.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___163_8021.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____8022,None ) ->
                   ((let uu____8029 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8029
                     then
                       let uu____8030 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____8031 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____8032 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____8033 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____8030
                         uu____8031 uu____8032 uu____8033
                     else ());
                    (let uu____8035 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____8035 with
                     | (head11,args1) ->
                         let uu____8061 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____8061 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8106 =
                                  let uu____8107 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____8108 = args_to_string args1 in
                                  let uu____8109 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____8110 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8107 uu____8108 uu____8109
                                    uu____8110 in
                                giveup env1 uu____8106 orig
                              else
                                (let uu____8112 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8117 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____8117 = FStar_Syntax_Util.Equal) in
                                 if uu____8112
                                 then
                                   let uu____8118 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____8118 with
                                   | USolved wl2 ->
                                       let uu____8120 =
                                         solve_prob orig None [] wl2 in
                                       solve env1 uu____8120
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8124 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____8124 with
                                    | (base1,refinement1) ->
                                        let uu____8150 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____8150 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____8204 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____8204 with
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
                                                           (fun uu____8214 
                                                              ->
                                                              fun uu____8215 
                                                                ->
                                                                match 
                                                                  (uu____8214,
                                                                    uu____8215)
                                                                with
                                                                | ((a,uu____8225),
                                                                   (a',uu____8227))
                                                                    ->
                                                                    let uu____8232
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
                                                                    uu____8232)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____8238 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8238 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8242 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___164_8275 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___164_8275.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___164_8275.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___164_8275.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___164_8275.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___164_8275.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___164_8275.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___164_8275.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___164_8275.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____8295 = p in
          match uu____8295 with
          | (((u,k),xs,c),ps,(h,uu____8306,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8355 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____8355 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8369 = h gs_xs in
                     let uu____8370 =
                       let uu____8377 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_60  -> FStar_Util.Inl _0_60) in
                       FStar_All.pipe_right uu____8377
                         (fun _0_61  -> Some _0_61) in
                     FStar_Syntax_Util.abs xs1 uu____8369 uu____8370 in
                   ((let uu____8408 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8408
                     then
                       let uu____8409 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____8410 = FStar_Syntax_Print.comp_to_string c in
                       let uu____8411 = FStar_Syntax_Print.term_to_string im in
                       let uu____8412 = FStar_Syntax_Print.tag_of_term im in
                       let uu____8413 =
                         let uu____8414 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____8414
                           (FStar_String.concat ", ") in
                       let uu____8417 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8409 uu____8410 uu____8411 uu____8412
                         uu____8413 uu____8417
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___130_8435 =
          match uu___130_8435 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____8464 = p in
          match uu____8464 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8522 = FStar_List.nth ps i in
              (match uu____8522 with
               | (pi,uu____8525) ->
                   let uu____8530 = FStar_List.nth xs i in
                   (match uu____8530 with
                    | (xi,uu____8537) ->
                        let rec gs k =
                          let uu____8546 = FStar_Syntax_Util.arrow_formals k in
                          match uu____8546 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8598)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8606 = new_uvar r xs k_a in
                                    (match uu____8606 with
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
                                         let uu____8625 = aux subst2 tl1 in
                                         (match uu____8625 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8640 =
                                                let uu____8642 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8642 :: gi_xs' in
                                              let uu____8643 =
                                                let uu____8645 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8645 :: gi_ps' in
                                              (uu____8640, uu____8643))) in
                              aux [] bs in
                        let uu____8648 =
                          let uu____8649 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8649 in
                        if uu____8648
                        then None
                        else
                          (let uu____8652 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8652 with
                           | (g_xs,uu____8659) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8666 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r in
                                 let uu____8671 =
                                   let uu____8678 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_62  -> FStar_Util.Inl _0_62) in
                                   FStar_All.pipe_right uu____8678
                                     (fun _0_63  -> Some _0_63) in
                                 FStar_Syntax_Util.abs xs uu____8666
                                   uu____8671 in
                               let sub1 =
                                 let uu____8709 =
                                   let uu____8712 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let uu____8719 =
                                     let uu____8722 =
                                       FStar_List.map
                                         (fun uu____8728  ->
                                            match uu____8728 with
                                            | (uu____8733,uu____8734,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____8722 in
                                   mk_problem (p_scope orig) orig uu____8712
                                     (p_rel orig) uu____8719 None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____8709 in
                               ((let uu____8744 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____8744
                                 then
                                   let uu____8745 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____8746 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8745 uu____8746
                                 else ());
                                (let wl2 =
                                   let uu____8749 =
                                     let uu____8751 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives.fst (p_guard sub1) in
                                     Some uu____8751 in
                                   solve_prob orig uu____8749
                                     [TERM (u, proj)] wl1 in
                                 let uu____8756 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_65  -> Some _0_65) uu____8756))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8780 = lhs in
          match uu____8780 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8803 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____8803 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8829 =
                        let uu____8855 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____8855) in
                      Some uu____8829
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____8938 =
                           let uu____8942 =
                             let uu____8943 = FStar_Syntax_Subst.compress k in
                             uu____8943.FStar_Syntax_Syntax.n in
                           (uu____8942, args) in
                         match uu____8938 with
                         | (uu____8950,[]) ->
                             let uu____8952 =
                               let uu____8958 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____8958) in
                             Some uu____8952
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____8969,uu____8970) ->
                             let uu____8981 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____8981 with
                              | (uv1,uv_args) ->
                                  let uu____9010 =
                                    let uu____9011 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9011.FStar_Syntax_Syntax.n in
                                  (match uu____9010 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9018) ->
                                       let uu____9031 =
                                         pat_vars env [] uv_args in
                                       (match uu____9031 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9045  ->
                                                      let uu____9046 =
                                                        let uu____9047 =
                                                          let uu____9048 =
                                                            let uu____9051 =
                                                              let uu____9052
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9052
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9051 in
                                                          fst uu____9048 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9047 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9046)) in
                                            let c1 =
                                              let uu____9058 =
                                                let uu____9059 =
                                                  let uu____9062 =
                                                    let uu____9063 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9063
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9062 in
                                                fst uu____9059 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9058 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9072 =
                                                let uu____9079 =
                                                  let uu____9085 =
                                                    let uu____9086 =
                                                      let uu____9089 =
                                                        let uu____9090 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9090
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9089 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9086 in
                                                  FStar_Util.Inl uu____9085 in
                                                Some uu____9079 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9072 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9110 -> None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9113,uu____9114)
                             ->
                             let uu____9126 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9126 with
                              | (uv1,uv_args) ->
                                  let uu____9155 =
                                    let uu____9156 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9156.FStar_Syntax_Syntax.n in
                                  (match uu____9155 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9163) ->
                                       let uu____9176 =
                                         pat_vars env [] uv_args in
                                       (match uu____9176 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9190  ->
                                                      let uu____9191 =
                                                        let uu____9192 =
                                                          let uu____9193 =
                                                            let uu____9196 =
                                                              let uu____9197
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9197
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9196 in
                                                          fst uu____9193 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9192 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9191)) in
                                            let c1 =
                                              let uu____9203 =
                                                let uu____9204 =
                                                  let uu____9207 =
                                                    let uu____9208 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9208
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9207 in
                                                fst uu____9204 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9203 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9217 =
                                                let uu____9224 =
                                                  let uu____9230 =
                                                    let uu____9231 =
                                                      let uu____9234 =
                                                        let uu____9235 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9235
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9234 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9231 in
                                                  FStar_Util.Inl uu____9230 in
                                                Some uu____9224 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9217 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9255 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9260)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____9292 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____9292
                                 (fun _0_66  -> Some _0_66)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9316 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____9316 with
                                  | (args1,rest) ->
                                      let uu____9334 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____9334 with
                                       | (xs2,c2) ->
                                           let uu____9342 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____9342
                                             (fun uu____9353  ->
                                                match uu____9353 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9375 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____9375 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____9423 =
                                        let uu____9426 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9426 in
                                      FStar_All.pipe_right uu____9423
                                        (fun _0_67  -> Some _0_67))
                         | uu____9434 ->
                             let uu____9438 =
                               let uu____9439 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____9440 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____9441 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9439 uu____9440 uu____9441 in
                             failwith uu____9438 in
                       let uu____9445 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____9445
                         (fun uu____9473  ->
                            match uu____9473 with
                            | (xs1,c1) ->
                                let uu____9501 =
                                  let uu____9524 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9524) in
                                Some uu____9501)) in
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
                     let uu____9596 = imitate orig env wl1 st in
                     match uu____9596 with
                     | Failed uu____9601 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9607 = project orig env wl1 i st in
                      match uu____9607 with
                      | None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some (Failed uu____9614) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____9628 = FStar_Syntax_Util.head_and_args t21 in
                match uu____9628 with
                | (hd1,uu____9639) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9654 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9662 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9663 -> true
                     | uu____9678 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____9681 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____9681
                         then true
                         else
                           ((let uu____9684 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____9684
                             then
                               let uu____9685 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9685
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9693 =
                    let uu____9696 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____9696 FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____9693 FStar_Syntax_Free.names in
                let uu____9727 = FStar_Util.set_is_empty fvs_hd in
                if uu____9727
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____9736 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____9736 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9744 =
                            let uu____9745 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____9745 in
                          giveup_or_defer1 orig uu____9744
                        else
                          (let uu____9747 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____9747
                           then
                             let uu____9748 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____9748
                              then
                                let uu____9749 = subterms args_lhs in
                                imitate' orig env wl1 uu____9749
                              else
                                ((let uu____9753 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____9753
                                  then
                                    let uu____9754 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____9755 = names_to_string fvs1 in
                                    let uu____9756 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9754 uu____9755 uu____9756
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9761 ->
                                        let uu____9762 = sn_binders env vars in
                                        u_abs k_uv uu____9762 t21 in
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
                               (let uu____9771 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____9771
                                then
                                  ((let uu____9773 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____9773
                                    then
                                      let uu____9774 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____9775 = names_to_string fvs1 in
                                      let uu____9776 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9774 uu____9775 uu____9776
                                    else ());
                                   (let uu____9778 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9778
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
                     (let uu____9792 =
                        let uu____9793 = FStar_Syntax_Free.names t1 in
                        check_head uu____9793 t2 in
                      if uu____9792
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____9797 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____9797
                          then
                            let uu____9798 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9798
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9801 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9801 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9846 =
               match uu____9846 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k in
                   let uu____9877 = FStar_Syntax_Util.arrow_formals k1 in
                   (match uu____9877 with
                    | (all_formals,uu____9888) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____9980  ->
                                        match uu____9980 with
                                        | (x,imp) ->
                                            let uu____9987 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____9987, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____9995 = FStar_Syntax_Util.type_u () in
                                match uu____9995 with
                                | (t1,uu____9999) ->
                                    let uu____10000 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    fst uu____10000 in
                              let uu____10003 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____10003 with
                               | (t',tm_u1) ->
                                   let uu____10010 = destruct_flex_t t' in
                                   (match uu____10010 with
                                    | (uu____10030,u1,k11,uu____10033) ->
                                        let sol =
                                          let uu____10061 =
                                            let uu____10066 =
                                              u_abs k1 all_formals t' in
                                            ((u, k1), uu____10066) in
                                          TERM uu____10061 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10126 = pat_var_opt env pat_args hd1 in
                              (match uu____10126 with
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
                                              (fun uu____10155  ->
                                                 match uu____10155 with
                                                 | (x,uu____10159) ->
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
                                      let uu____10165 =
                                        let uu____10166 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____10166 in
                                      if uu____10165
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10170 =
                                           FStar_Util.set_add (fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10170 formals1
                                           tl1)))
                          | uu____10176 -> failwith "Impossible" in
                        let uu____10187 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____10187 all_formals args) in
             let solve_both_pats wl1 uu____10227 uu____10228 r =
               match (uu____10227, uu____10228) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10342 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____10342
                   then
                     let uu____10343 = solve_prob orig None [] wl1 in
                     solve env uu____10343
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____10358 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____10358
                       then
                         let uu____10359 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____10360 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____10361 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____10362 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____10363 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10359 uu____10360 uu____10361 uu____10362
                           uu____10363
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____10411 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____10411 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10424 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____10424 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10456 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10456 in
                                  let uu____10459 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____10459 k3)
                           else
                             (let uu____10462 =
                                let uu____10463 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____10464 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____10465 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10463 uu____10464 uu____10465 in
                              failwith uu____10462) in
                       let uu____10466 =
                         let uu____10472 =
                           let uu____10480 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____10480 in
                         match uu____10472 with
                         | (bs,k1') ->
                             let uu____10498 =
                               let uu____10506 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____10506 in
                             (match uu____10498 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____10527 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_68  ->
                                         FStar_TypeChecker_Common.TProb _0_68)
                                      uu____10527 in
                                  let uu____10532 =
                                    let uu____10535 =
                                      let uu____10536 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____10536.FStar_Syntax_Syntax.n in
                                    let uu____10539 =
                                      let uu____10540 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____10540.FStar_Syntax_Syntax.n in
                                    (uu____10535, uu____10539) in
                                  (match uu____10532 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10548,uu____10549) ->
                                       (k1', [sub_prob])
                                   | (uu____10553,FStar_Syntax_Syntax.Tm_type
                                      uu____10554) -> (k2', [sub_prob])
                                   | uu____10558 ->
                                       let uu____10561 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____10561 with
                                        | (t,uu____10570) ->
                                            let uu____10571 = new_uvar r zs t in
                                            (match uu____10571 with
                                             | (k_zs,uu____10580) ->
                                                 let kprob =
                                                   let uu____10582 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_69  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_69) uu____10582 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____10466 with
                       | (k_u',sub_probs) ->
                           let uu____10596 =
                             let uu____10604 =
                               let uu____10605 = new_uvar r zs k_u' in
                               FStar_All.pipe_left FStar_Pervasives.fst
                                 uu____10605 in
                             let uu____10610 =
                               let uu____10613 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____10613 in
                             let uu____10616 =
                               let uu____10619 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____10619 in
                             (uu____10604, uu____10610, uu____10616) in
                           (match uu____10596 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____10638 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____10638 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____10650 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____10650
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____10654 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____10654 with
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
             let solve_one_pat uu____10686 uu____10687 =
               match (uu____10686, uu____10687) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10751 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____10751
                     then
                       let uu____10752 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10753 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10752 uu____10753
                     else ());
                    (let uu____10755 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____10755
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10762  ->
                              fun uu____10763  ->
                                match (uu____10762, uu____10763) with
                                | ((a,uu____10773),(t21,uu____10775)) ->
                                    let uu____10780 =
                                      let uu____10783 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____10783
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____10780
                                      (fun _0_70  ->
                                         FStar_TypeChecker_Common.TProb _0_70))
                           xs args2 in
                       let guard =
                         let uu____10787 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____10787 in
                       let wl1 = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____10797 = occurs_check env wl (u1, k1) t21 in
                        match uu____10797 with
                        | (occurs_ok,uu____10802) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____10807 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____10807
                            then
                              let sol =
                                let uu____10809 =
                                  let uu____10814 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____10814) in
                                TERM uu____10809 in
                              let wl1 = solve_prob orig None [sol] wl in
                              solve env wl1
                            else
                              (let uu____10819 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____10819
                               then
                                 let uu____10820 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____10820 with
                                 | (sol,(uu____10830,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____10840 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____10840
                                       then
                                         let uu____10841 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10841
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10846 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____10848 = lhs in
             match uu____10848 with
             | (t1,u1,k1,args1) ->
                 let uu____10853 = rhs in
                 (match uu____10853 with
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
                       | uu____10879 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____10885 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____10885 with
                              | (sol,uu____10892) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____10895 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____10895
                                    then
                                      let uu____10896 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____10896
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____10901 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____10903 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____10903
        then
          let uu____10904 = solve_prob orig None [] wl in
          solve env uu____10904
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____10908 = FStar_Util.physical_equality t1 t2 in
           if uu____10908
           then
             let uu____10909 = solve_prob orig None [] wl in
             solve env uu____10909
           else
             ((let uu____10912 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____10912
               then
                 let uu____10913 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____10913
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____10916,uu____10917) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____10918,FStar_Syntax_Syntax.Tm_bvar uu____10919) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___131_10959 =
                     match uu___131_10959 with
                     | [] -> c
                     | bs ->
                         let uu____10973 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c)) None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____10973 in
                   let uu____10983 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____10983 with
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
                                   let uu____11069 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____11069
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____11071 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_71  ->
                                      FStar_TypeChecker_Common.CProb _0_71)
                                   uu____11071))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___132_11148 =
                     match uu___132_11148 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l)) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____11183 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____11183 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11266 =
                                   let uu____11269 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____11270 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____11269
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11270 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_72  ->
                                      FStar_TypeChecker_Common.TProb _0_72)
                                   uu____11266))
               | (FStar_Syntax_Syntax.Tm_abs uu____11273,uu____11274) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11297 -> true
                     | uu____11312 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11340 =
                     let uu____11351 = maybe_eta t1 in
                     let uu____11356 = maybe_eta t2 in
                     (uu____11351, uu____11356) in
                   (match uu____11340 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___165_11387 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___165_11387.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___165_11387.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___165_11387.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___165_11387.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___165_11387.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___165_11387.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___165_11387.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___165_11387.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11406 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11406
                        then
                          let uu____11407 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11407 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11428 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11428
                        then
                          let uu____11429 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11429 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11434 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11445,FStar_Syntax_Syntax.Tm_abs uu____11446) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11469 -> true
                     | uu____11484 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11512 =
                     let uu____11523 = maybe_eta t1 in
                     let uu____11528 = maybe_eta t2 in
                     (uu____11523, uu____11528) in
                   (match uu____11512 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___165_11559 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___165_11559.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___165_11559.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___165_11559.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___165_11559.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___165_11559.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___165_11559.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___165_11559.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___165_11559.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11578 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11578
                        then
                          let uu____11579 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11579 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11600 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11600
                        then
                          let uu____11601 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11601 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11606 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11617,FStar_Syntax_Syntax.Tm_refine uu____11618) ->
                   let uu____11627 = as_refinement env wl t1 in
                   (match uu____11627 with
                    | (x1,phi1) ->
                        let uu____11632 = as_refinement env wl t2 in
                        (match uu____11632 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11638 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_73  ->
                                    FStar_TypeChecker_Common.TProb _0_73)
                                 uu____11638 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____11671 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____11671
                                 (guard_on_element wl problem x11) in
                             let fallback uu____11675 =
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
                                 let uu____11681 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____11681 impl in
                               let wl1 = solve_prob orig (Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11688 =
                                   let uu____11691 =
                                     let uu____11692 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____11692 :: (p_scope orig) in
                                   mk_problem uu____11691 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_74  ->
                                      FStar_TypeChecker_Common.TProb _0_74)
                                   uu____11688 in
                               let uu____11695 =
                                 solve env1
                                   (let uu___166_11696 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___166_11696.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___166_11696.smt_ok);
                                      tcenv = (uu___166_11696.tcenv)
                                    }) in
                               (match uu____11695 with
                                | Failed uu____11700 -> fallback ()
                                | Success uu____11703 ->
                                    let guard =
                                      let uu____11707 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives.fst in
                                      let uu____11710 =
                                        let uu____11711 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives.fst in
                                        FStar_All.pipe_right uu____11711
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____11707
                                        uu____11710 in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl2 =
                                      let uu___167_11718 = wl1 in
                                      {
                                        attempting =
                                          (uu___167_11718.attempting);
                                        wl_deferred =
                                          (uu___167_11718.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___167_11718.defer_ok);
                                        smt_ok = (uu___167_11718.smt_ok);
                                        tcenv = (uu___167_11718.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11720,FStar_Syntax_Syntax.Tm_uvar uu____11721) ->
                   let uu____11738 = destruct_flex_t t1 in
                   let uu____11739 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11738 uu____11739
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11740;
                     FStar_Syntax_Syntax.tk = uu____11741;
                     FStar_Syntax_Syntax.pos = uu____11742;
                     FStar_Syntax_Syntax.vars = uu____11743;_},uu____11744),FStar_Syntax_Syntax.Tm_uvar
                  uu____11745) ->
                   let uu____11776 = destruct_flex_t t1 in
                   let uu____11777 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11776 uu____11777
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11778,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11779;
                     FStar_Syntax_Syntax.tk = uu____11780;
                     FStar_Syntax_Syntax.pos = uu____11781;
                     FStar_Syntax_Syntax.vars = uu____11782;_},uu____11783))
                   ->
                   let uu____11814 = destruct_flex_t t1 in
                   let uu____11815 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11814 uu____11815
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11816;
                     FStar_Syntax_Syntax.tk = uu____11817;
                     FStar_Syntax_Syntax.pos = uu____11818;
                     FStar_Syntax_Syntax.vars = uu____11819;_},uu____11820),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11821;
                     FStar_Syntax_Syntax.tk = uu____11822;
                     FStar_Syntax_Syntax.pos = uu____11823;
                     FStar_Syntax_Syntax.vars = uu____11824;_},uu____11825))
                   ->
                   let uu____11870 = destruct_flex_t t1 in
                   let uu____11871 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11870 uu____11871
               | (FStar_Syntax_Syntax.Tm_uvar uu____11872,uu____11873) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11882 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11882 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11886;
                     FStar_Syntax_Syntax.tk = uu____11887;
                     FStar_Syntax_Syntax.pos = uu____11888;
                     FStar_Syntax_Syntax.vars = uu____11889;_},uu____11890),uu____11891)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11914 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11914 t2 wl
               | (uu____11918,FStar_Syntax_Syntax.Tm_uvar uu____11919) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____11928,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11929;
                     FStar_Syntax_Syntax.tk = uu____11930;
                     FStar_Syntax_Syntax.pos = uu____11931;
                     FStar_Syntax_Syntax.vars = uu____11932;_},uu____11933))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11956,FStar_Syntax_Syntax.Tm_type uu____11957) ->
                   solve_t' env
                     (let uu___168_11966 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_11966.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_11966.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_11966.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_11966.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_11966.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_11966.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_11966.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_11966.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_11966.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11967;
                     FStar_Syntax_Syntax.tk = uu____11968;
                     FStar_Syntax_Syntax.pos = uu____11969;
                     FStar_Syntax_Syntax.vars = uu____11970;_},uu____11971),FStar_Syntax_Syntax.Tm_type
                  uu____11972) ->
                   solve_t' env
                     (let uu___168_11995 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_11995.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_11995.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_11995.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_11995.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_11995.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_11995.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_11995.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_11995.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_11995.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11996,FStar_Syntax_Syntax.Tm_arrow uu____11997) ->
                   solve_t' env
                     (let uu___168_12013 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_12013.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_12013.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_12013.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_12013.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_12013.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_12013.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_12013.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_12013.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_12013.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12014;
                     FStar_Syntax_Syntax.tk = uu____12015;
                     FStar_Syntax_Syntax.pos = uu____12016;
                     FStar_Syntax_Syntax.vars = uu____12017;_},uu____12018),FStar_Syntax_Syntax.Tm_arrow
                  uu____12019) ->
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
               | (FStar_Syntax_Syntax.Tm_uvar uu____12050,uu____12051) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12062 =
                        let uu____12063 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12063 in
                      if uu____12062
                      then
                        let uu____12064 =
                          FStar_All.pipe_left
                            (fun _0_75  ->
                               FStar_TypeChecker_Common.TProb _0_75)
                            (let uu___169_12067 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_12067.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_12067.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_12067.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_12067.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_12067.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___169_12067.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_12067.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_12067.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_12067.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12068 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12064 uu____12068 t2
                          wl
                      else
                        (let uu____12073 = base_and_refinement env wl t2 in
                         match uu____12073 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12103 =
                                    FStar_All.pipe_left
                                      (fun _0_76  ->
                                         FStar_TypeChecker_Common.TProb _0_76)
                                      (let uu___170_12106 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___170_12106.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___170_12106.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___170_12106.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___170_12106.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___170_12106.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___170_12106.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___170_12106.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___170_12106.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___170_12106.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12107 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12103
                                    uu____12107 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___171_12122 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___171_12122.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___171_12122.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12125 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_77  ->
                                         FStar_TypeChecker_Common.TProb _0_77)
                                      uu____12125 in
                                  let guard =
                                    let uu____12133 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12133
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12139;
                     FStar_Syntax_Syntax.tk = uu____12140;
                     FStar_Syntax_Syntax.pos = uu____12141;
                     FStar_Syntax_Syntax.vars = uu____12142;_},uu____12143),uu____12144)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12169 =
                        let uu____12170 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12170 in
                      if uu____12169
                      then
                        let uu____12171 =
                          FStar_All.pipe_left
                            (fun _0_78  ->
                               FStar_TypeChecker_Common.TProb _0_78)
                            (let uu___169_12174 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_12174.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_12174.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_12174.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_12174.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_12174.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___169_12174.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_12174.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_12174.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_12174.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12175 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12171 uu____12175 t2
                          wl
                      else
                        (let uu____12180 = base_and_refinement env wl t2 in
                         match uu____12180 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12210 =
                                    FStar_All.pipe_left
                                      (fun _0_79  ->
                                         FStar_TypeChecker_Common.TProb _0_79)
                                      (let uu___170_12213 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___170_12213.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___170_12213.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___170_12213.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___170_12213.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___170_12213.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___170_12213.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___170_12213.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___170_12213.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___170_12213.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12214 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12210
                                    uu____12214 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___171_12229 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___171_12229.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___171_12229.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12232 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_80  ->
                                         FStar_TypeChecker_Common.TProb _0_80)
                                      uu____12232 in
                                  let guard =
                                    let uu____12240 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12240
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12246,FStar_Syntax_Syntax.Tm_uvar uu____12247) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12257 = base_and_refinement env wl t1 in
                      match uu____12257 with
                      | (t_base,uu____12268) ->
                          solve_t env
                            (let uu___172_12283 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___172_12283.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___172_12283.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___172_12283.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___172_12283.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___172_12283.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___172_12283.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___172_12283.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___172_12283.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12286,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12287;
                     FStar_Syntax_Syntax.tk = uu____12288;
                     FStar_Syntax_Syntax.pos = uu____12289;
                     FStar_Syntax_Syntax.vars = uu____12290;_},uu____12291))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12315 = base_and_refinement env wl t1 in
                      match uu____12315 with
                      | (t_base,uu____12326) ->
                          solve_t env
                            (let uu___172_12341 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___172_12341.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___172_12341.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___172_12341.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___172_12341.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___172_12341.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___172_12341.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___172_12341.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___172_12341.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12344,uu____12345) ->
                   let t21 =
                     let uu____12353 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____12353 in
                   solve_t env
                     (let uu___173_12366 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_12366.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___173_12366.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___173_12366.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___173_12366.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_12366.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_12366.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_12366.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_12366.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_12366.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12367,FStar_Syntax_Syntax.Tm_refine uu____12368) ->
                   let t11 =
                     let uu____12376 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____12376 in
                   solve_t env
                     (let uu___174_12389 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_12389.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___174_12389.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___174_12389.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___174_12389.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_12389.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_12389.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_12389.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_12389.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_12389.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12392,uu____12393) ->
                   let head1 =
                     let uu____12412 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12412 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12443 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12443 FStar_Pervasives.fst in
                   let uu____12471 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12471
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12480 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12480
                      then
                        let guard =
                          let uu____12487 =
                            let uu____12488 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12488 = FStar_Syntax_Util.Equal in
                          if uu____12487
                          then None
                          else
                            (let uu____12491 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_81  -> Some _0_81)
                               uu____12491) in
                        let uu____12493 = solve_prob orig guard [] wl in
                        solve env uu____12493
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12496,uu____12497) ->
                   let head1 =
                     let uu____12505 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12505 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12536 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12536 FStar_Pervasives.fst in
                   let uu____12564 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12564
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12573 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12573
                      then
                        let guard =
                          let uu____12580 =
                            let uu____12581 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12581 = FStar_Syntax_Util.Equal in
                          if uu____12580
                          then None
                          else
                            (let uu____12584 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_82  -> Some _0_82)
                               uu____12584) in
                        let uu____12586 = solve_prob orig guard [] wl in
                        solve env uu____12586
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12589,uu____12590) ->
                   let head1 =
                     let uu____12594 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12594 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12625 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12625 FStar_Pervasives.fst in
                   let uu____12653 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12653
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12662 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12662
                      then
                        let guard =
                          let uu____12669 =
                            let uu____12670 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12670 = FStar_Syntax_Util.Equal in
                          if uu____12669
                          then None
                          else
                            (let uu____12673 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_83  -> Some _0_83)
                               uu____12673) in
                        let uu____12675 = solve_prob orig guard [] wl in
                        solve env uu____12675
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12678,uu____12679) ->
                   let head1 =
                     let uu____12683 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12683 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12714 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12714 FStar_Pervasives.fst in
                   let uu____12742 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12742
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12751 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12751
                      then
                        let guard =
                          let uu____12758 =
                            let uu____12759 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12759 = FStar_Syntax_Util.Equal in
                          if uu____12758
                          then None
                          else
                            (let uu____12762 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_84  -> Some _0_84)
                               uu____12762) in
                        let uu____12764 = solve_prob orig guard [] wl in
                        solve env uu____12764
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____12767,uu____12768) ->
                   let head1 =
                     let uu____12772 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12772 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12803 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12803 FStar_Pervasives.fst in
                   let uu____12831 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12831
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12840 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12840
                      then
                        let guard =
                          let uu____12847 =
                            let uu____12848 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12848 = FStar_Syntax_Util.Equal in
                          if uu____12847
                          then None
                          else
                            (let uu____12851 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_85  -> Some _0_85)
                               uu____12851) in
                        let uu____12853 = solve_prob orig guard [] wl in
                        solve env uu____12853
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____12856,uu____12857) ->
                   let head1 =
                     let uu____12870 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12870 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12901 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12901 FStar_Pervasives.fst in
                   let uu____12929 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12929
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12938 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12938
                      then
                        let guard =
                          let uu____12945 =
                            let uu____12946 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12946 = FStar_Syntax_Util.Equal in
                          if uu____12945
                          then None
                          else
                            (let uu____12949 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_86  -> Some _0_86)
                               uu____12949) in
                        let uu____12951 = solve_prob orig guard [] wl in
                        solve env uu____12951
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12954,FStar_Syntax_Syntax.Tm_match uu____12955) ->
                   let head1 =
                     let uu____12974 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12974 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13005 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13005 FStar_Pervasives.fst in
                   let uu____13033 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13033
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13042 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13042
                      then
                        let guard =
                          let uu____13049 =
                            let uu____13050 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13050 = FStar_Syntax_Util.Equal in
                          if uu____13049
                          then None
                          else
                            (let uu____13053 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_87  -> Some _0_87)
                               uu____13053) in
                        let uu____13055 = solve_prob orig guard [] wl in
                        solve env uu____13055
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13058,FStar_Syntax_Syntax.Tm_uinst uu____13059) ->
                   let head1 =
                     let uu____13067 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13067 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13098 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13098 FStar_Pervasives.fst in
                   let uu____13126 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13126
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13135 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13135
                      then
                        let guard =
                          let uu____13142 =
                            let uu____13143 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13143 = FStar_Syntax_Util.Equal in
                          if uu____13142
                          then None
                          else
                            (let uu____13146 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_88  -> Some _0_88)
                               uu____13146) in
                        let uu____13148 = solve_prob orig guard [] wl in
                        solve env uu____13148
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13151,FStar_Syntax_Syntax.Tm_name uu____13152) ->
                   let head1 =
                     let uu____13156 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13156 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13187 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13187 FStar_Pervasives.fst in
                   let uu____13215 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13215
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13224 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13224
                      then
                        let guard =
                          let uu____13231 =
                            let uu____13232 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13232 = FStar_Syntax_Util.Equal in
                          if uu____13231
                          then None
                          else
                            (let uu____13235 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_89  -> Some _0_89)
                               uu____13235) in
                        let uu____13237 = solve_prob orig guard [] wl in
                        solve env uu____13237
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13240,FStar_Syntax_Syntax.Tm_constant uu____13241) ->
                   let head1 =
                     let uu____13245 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13245 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13276 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13276 FStar_Pervasives.fst in
                   let uu____13304 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13304
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13313 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13313
                      then
                        let guard =
                          let uu____13320 =
                            let uu____13321 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13321 = FStar_Syntax_Util.Equal in
                          if uu____13320
                          then None
                          else
                            (let uu____13324 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_90  -> Some _0_90)
                               uu____13324) in
                        let uu____13326 = solve_prob orig guard [] wl in
                        solve env uu____13326
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13329,FStar_Syntax_Syntax.Tm_fvar uu____13330) ->
                   let head1 =
                     let uu____13334 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13334 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13365 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13365 FStar_Pervasives.fst in
                   let uu____13393 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13393
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13402 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13402
                      then
                        let guard =
                          let uu____13409 =
                            let uu____13410 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13410 = FStar_Syntax_Util.Equal in
                          if uu____13409
                          then None
                          else
                            (let uu____13413 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_91  -> Some _0_91)
                               uu____13413) in
                        let uu____13415 = solve_prob orig guard [] wl in
                        solve env uu____13415
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13418,FStar_Syntax_Syntax.Tm_app uu____13419) ->
                   let head1 =
                     let uu____13432 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13432 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13463 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13463 FStar_Pervasives.fst in
                   let uu____13491 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13491
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13500 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13500
                      then
                        let guard =
                          let uu____13507 =
                            let uu____13508 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13508 = FStar_Syntax_Util.Equal in
                          if uu____13507
                          then None
                          else
                            (let uu____13511 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_92  -> Some _0_92)
                               uu____13511) in
                        let uu____13513 = solve_prob orig guard [] wl in
                        solve env uu____13513
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13517,uu____13518),uu____13519) ->
                   solve_t' env
                     (let uu___175_13548 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_13548.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_13548.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_13548.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_13548.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_13548.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_13548.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_13548.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_13548.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_13548.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13551,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13553,uu____13554)) ->
                   solve_t' env
                     (let uu___176_13583 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_13583.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___176_13583.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___176_13583.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___176_13583.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_13583.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_13583.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_13583.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_13583.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_13583.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13584,uu____13585) ->
                   let uu____13593 =
                     let uu____13594 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13595 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13594
                       uu____13595 in
                   failwith uu____13593
               | (FStar_Syntax_Syntax.Tm_meta uu____13596,uu____13597) ->
                   let uu____13602 =
                     let uu____13603 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13604 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13603
                       uu____13604 in
                   failwith uu____13602
               | (FStar_Syntax_Syntax.Tm_delayed uu____13605,uu____13606) ->
                   let uu____13627 =
                     let uu____13628 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13629 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13628
                       uu____13629 in
                   failwith uu____13627
               | (uu____13630,FStar_Syntax_Syntax.Tm_meta uu____13631) ->
                   let uu____13636 =
                     let uu____13637 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13638 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13637
                       uu____13638 in
                   failwith uu____13636
               | (uu____13639,FStar_Syntax_Syntax.Tm_delayed uu____13640) ->
                   let uu____13661 =
                     let uu____13662 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13663 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13662
                       uu____13663 in
                   failwith uu____13661
               | (uu____13664,FStar_Syntax_Syntax.Tm_let uu____13665) ->
                   let uu____13673 =
                     let uu____13674 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13675 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13674
                       uu____13675 in
                   failwith uu____13673
               | uu____13676 -> giveup env "head tag mismatch" orig)))
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
          (let uu____13708 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____13708
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____13716  ->
                  fun uu____13717  ->
                    match (uu____13716, uu____13717) with
                    | ((a1,uu____13727),(a2,uu____13729)) ->
                        let uu____13734 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_93  -> FStar_TypeChecker_Common.TProb _0_93)
                          uu____13734)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____13740 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p) FStar_Pervasives.fst)
                 sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____13740 in
           let wl1 = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____13760 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____13767)::[] -> wp1
              | uu____13780 ->
                  let uu____13786 =
                    let uu____13787 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____13787 in
                  failwith uu____13786 in
            let uu____13790 =
              let uu____13796 =
                let uu____13797 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____13797 in
              [uu____13796] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____13790;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____13798 = lift_c1 () in solve_eq uu____13798 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___133_13802  ->
                       match uu___133_13802 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____13803 -> false)) in
             let uu____13804 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____13828)::uu____13829,(wp2,uu____13831)::uu____13832)
                   -> (wp1, wp2)
               | uu____13873 ->
                   let uu____13886 =
                     let uu____13887 =
                       let uu____13890 =
                         let uu____13891 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____13892 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____13891 uu____13892 in
                       (uu____13890, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____13887 in
                   raise uu____13886 in
             match uu____13804 with
             | (wpc1,wpc2) ->
                 let uu____13909 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____13909
                 then
                   let uu____13912 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env uu____13912 wl
                 else
                   (let uu____13916 =
                      let uu____13920 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____13920 in
                    match uu____13916 with
                    | (c2_decl,qualifiers) ->
                        let uu____13932 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____13932
                        then
                          let c1_repr =
                            let uu____13935 =
                              let uu____13936 =
                                let uu____13937 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____13937 in
                              let uu____13938 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13936 uu____13938 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13935 in
                          let c2_repr =
                            let uu____13940 =
                              let uu____13941 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____13942 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13941 uu____13942 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13940 in
                          let prob =
                            let uu____13944 =
                              let uu____13947 =
                                let uu____13948 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____13949 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____13948
                                  uu____13949 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____13947 in
                            FStar_TypeChecker_Common.TProb uu____13944 in
                          let wl1 =
                            let uu____13951 =
                              let uu____13953 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives.fst in
                              Some uu____13953 in
                            solve_prob orig uu____13951 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____13960 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____13960
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____13962 =
                                     let uu____13965 =
                                       let uu____13966 =
                                         let uu____13976 =
                                           let uu____13977 =
                                             let uu____13978 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____13978] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____13977 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____13979 =
                                           let uu____13981 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____13982 =
                                             let uu____13984 =
                                               let uu____13985 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____13985 in
                                             [uu____13984] in
                                           uu____13981 :: uu____13982 in
                                         (uu____13976, uu____13979) in
                                       FStar_Syntax_Syntax.Tm_app uu____13966 in
                                     FStar_Syntax_Syntax.mk uu____13965 in
                                   uu____13962
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____13996 =
                                    let uu____13999 =
                                      let uu____14000 =
                                        let uu____14010 =
                                          let uu____14011 =
                                            let uu____14012 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____14012] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____14011 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____14013 =
                                          let uu____14015 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____14016 =
                                            let uu____14018 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____14019 =
                                              let uu____14021 =
                                                let uu____14022 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14022 in
                                              [uu____14021] in
                                            uu____14018 :: uu____14019 in
                                          uu____14015 :: uu____14016 in
                                        (uu____14010, uu____14013) in
                                      FStar_Syntax_Syntax.Tm_app uu____14000 in
                                    FStar_Syntax_Syntax.mk uu____13999 in
                                  uu____13996
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____14033 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_94  ->
                                  FStar_TypeChecker_Common.TProb _0_94)
                               uu____14033 in
                           let wl1 =
                             let uu____14039 =
                               let uu____14041 =
                                 let uu____14044 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____14044 g in
                               FStar_All.pipe_left (fun _0_95  -> Some _0_95)
                                 uu____14041 in
                             solve_prob orig uu____14039 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____14054 = FStar_Util.physical_equality c1 c2 in
        if uu____14054
        then
          let uu____14055 = solve_prob orig None [] wl in
          solve env uu____14055
        else
          ((let uu____14058 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____14058
            then
              let uu____14059 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____14060 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14059
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14060
            else ());
           (let uu____14062 =
              let uu____14065 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____14066 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____14065, uu____14066) in
            match uu____14062 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14070),FStar_Syntax_Syntax.Total
                    (t2,uu____14072)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14085 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14085 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14088,FStar_Syntax_Syntax.Total uu____14089) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14101),FStar_Syntax_Syntax.Total
                    (t2,uu____14103)) ->
                     let uu____14116 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14116 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14120),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14122)) ->
                     let uu____14135 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14135 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14139),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14141)) ->
                     let uu____14154 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14154 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14157,FStar_Syntax_Syntax.Comp uu____14158) ->
                     let uu____14164 =
                       let uu___177_14167 = problem in
                       let uu____14170 =
                         let uu____14171 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14171 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14167.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14170;
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14167.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___177_14167.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___177_14167.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14167.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14167.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14167.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14167.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14167.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14164 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14172,FStar_Syntax_Syntax.Comp uu____14173) ->
                     let uu____14179 =
                       let uu___177_14182 = problem in
                       let uu____14185 =
                         let uu____14186 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14186 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14182.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14185;
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14182.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___177_14182.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___177_14182.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14182.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14182.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14182.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14182.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14182.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14179 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14187,FStar_Syntax_Syntax.GTotal uu____14188) ->
                     let uu____14194 =
                       let uu___178_14197 = problem in
                       let uu____14200 =
                         let uu____14201 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14201 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14197.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___178_14197.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14197.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14200;
                         FStar_TypeChecker_Common.element =
                           (uu___178_14197.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14197.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14197.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14197.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14197.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14197.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14194 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14202,FStar_Syntax_Syntax.Total uu____14203) ->
                     let uu____14209 =
                       let uu___178_14212 = problem in
                       let uu____14215 =
                         let uu____14216 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14216 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14212.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___178_14212.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14212.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14215;
                         FStar_TypeChecker_Common.element =
                           (uu___178_14212.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14212.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14212.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14212.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14212.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14212.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14209 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14217,FStar_Syntax_Syntax.Comp uu____14218) ->
                     let uu____14219 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____14219
                     then
                       let uu____14220 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type" in
                       solve_t env uu____14220 wl
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
                           (let uu____14230 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____14230
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14232 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____14232 with
                            | None  ->
                                let uu____14234 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14235 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____14235) in
                                if uu____14234
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
                                  (let uu____14238 =
                                     let uu____14239 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____14240 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14239 uu____14240 in
                                   giveup env uu____14238 orig)
                            | Some edge -> solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14245 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14261  ->
              match uu____14261 with
              | (uu____14268,uu____14269,u,uu____14271,uu____14272,uu____14273)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____14245 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14291 =
        FStar_All.pipe_right (fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____14291 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____14301 =
        FStar_All.pipe_right (snd ineqs)
          (FStar_List.map
             (fun uu____14313  ->
                match uu____14313 with
                | (u1,u2) ->
                    let uu____14318 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____14319 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____14318 uu____14319)) in
      FStar_All.pipe_right uu____14301 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14331,[])) -> "{}"
      | uu____14344 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14354 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____14354
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____14357 =
              FStar_List.map
                (fun uu____14361  ->
                   match uu____14361 with
                   | (uu____14364,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____14357 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____14368 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14368 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14406 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____14406
    then
      let uu____14407 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____14408 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14407
        (rel_to_string rel) uu____14408
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
            let uu____14428 =
              let uu____14430 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_96  -> Some _0_96) uu____14430 in
            FStar_Syntax_Syntax.new_bv uu____14428 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____14436 =
              let uu____14438 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_97  -> Some _0_97) uu____14438 in
            let uu____14440 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____14436 uu____14440 in
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
          let uu____14463 = FStar_Options.eager_inference () in
          if uu____14463
          then
            let uu___179_14464 = probs in
            {
              attempting = (uu___179_14464.attempting);
              wl_deferred = (uu___179_14464.wl_deferred);
              ctr = (uu___179_14464.ctr);
              defer_ok = false;
              smt_ok = (uu___179_14464.smt_ok);
              tcenv = (uu___179_14464.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Syntax_Unionfind.rollback tx;
             (let uu____14475 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____14475
              then
                let uu____14476 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____14476
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
          ((let uu____14486 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____14486
            then
              let uu____14487 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14487
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____14491 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____14491
             then
               let uu____14492 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14492
             else ());
            (let f2 =
               let uu____14495 =
                 let uu____14496 = FStar_Syntax_Util.unmeta f1 in
                 uu____14496.FStar_Syntax_Syntax.n in
               match uu____14495 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14500 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___180_14501 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___180_14501.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___180_14501.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___180_14501.FStar_TypeChecker_Env.implicits)
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
            let uu____14516 =
              let uu____14517 =
                let uu____14518 =
                  let uu____14519 =
                    FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____14519
                    (fun _0_98  -> FStar_TypeChecker_Common.NonTrivial _0_98) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14518;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____14517 in
            FStar_All.pipe_left (fun _0_99  -> Some _0_99) uu____14516
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____14552 =
        let uu____14553 =
          let uu____14554 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
          FStar_All.pipe_right uu____14554
            (fun _0_100  -> FStar_TypeChecker_Common.NonTrivial _0_100) in
        {
          FStar_TypeChecker_Env.guard_f = uu____14553;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      Some uu____14552
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
          (let uu____14580 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14580
           then
             let uu____14581 = FStar_Syntax_Print.term_to_string t1 in
             let uu____14582 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14581
               uu____14582
           else ());
          (let prob =
             let uu____14585 =
               let uu____14588 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____14588 in
             FStar_All.pipe_left
               (fun _0_101  -> FStar_TypeChecker_Common.TProb _0_101)
               uu____14585 in
           let g =
             let uu____14593 =
               let uu____14595 = singleton' env prob smt_ok in
               solve_and_commit env uu____14595 (fun uu____14596  -> None) in
             FStar_All.pipe_left (with_guard env prob) uu____14593 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14610 = try_teq true env t1 t2 in
        match uu____14610 with
        | None  ->
            let uu____14612 =
              let uu____14613 =
                let uu____14616 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                let uu____14617 = FStar_TypeChecker_Env.get_range env in
                (uu____14616, uu____14617) in
              FStar_Errors.Error uu____14613 in
            raise uu____14612
        | Some g ->
            ((let uu____14620 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____14620
              then
                let uu____14621 = FStar_Syntax_Print.term_to_string t1 in
                let uu____14622 = FStar_Syntax_Print.term_to_string t2 in
                let uu____14623 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14621
                  uu____14622 uu____14623
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
          (let uu____14639 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14639
           then
             let uu____14640 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____14641 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14640
               uu____14641
           else ());
          (let uu____14643 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____14643 with
           | (prob,x) ->
               let g =
                 let uu____14651 =
                   let uu____14653 = singleton' env prob smt_ok in
                   solve_and_commit env uu____14653
                     (fun uu____14654  -> None) in
                 FStar_All.pipe_left (with_guard env prob) uu____14651 in
               ((let uu____14660 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____14660
                 then
                   let uu____14661 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____14662 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____14663 =
                     let uu____14664 = FStar_Util.must g in
                     guard_to_string env uu____14664 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14661 uu____14662 uu____14663
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
          let uu____14688 = FStar_TypeChecker_Env.get_range env in
          let uu____14689 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.err uu____14688 uu____14689
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____14701 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____14701
         then
           let uu____14702 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____14703 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____14702
             uu____14703
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____14708 =
             let uu____14711 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None uu____14711 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_102  -> FStar_TypeChecker_Common.CProb _0_102)
             uu____14708 in
         let uu____14714 =
           let uu____14716 = singleton env prob in
           solve_and_commit env uu____14716 (fun uu____14717  -> None) in
         FStar_All.pipe_left (with_guard env prob) uu____14714)
let solve_universe_inequalities':
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____14736  ->
        match uu____14736 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____14761 =
                 let uu____14762 =
                   let uu____14765 =
                     let uu____14766 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____14767 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____14766 uu____14767 in
                   let uu____14768 = FStar_TypeChecker_Env.get_range env in
                   (uu____14765, uu____14768) in
                 FStar_Errors.Error uu____14762 in
               raise uu____14761) in
            let equiv1 v1 v' =
              let uu____14776 =
                let uu____14779 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____14780 = FStar_Syntax_Subst.compress_univ v' in
                (uu____14779, uu____14780) in
              match uu____14776 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____14787 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____14801 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____14801 with
                      | FStar_Syntax_Syntax.U_unif uu____14805 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____14816  ->
                                    match uu____14816 with
                                    | (u,v') ->
                                        let uu____14822 = equiv1 v1 v' in
                                        if uu____14822
                                        then
                                          let uu____14824 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____14824 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____14834 -> [])) in
            let uu____14837 =
              let wl =
                let uu___181_14840 = empty_worklist env in
                {
                  attempting = (uu___181_14840.attempting);
                  wl_deferred = (uu___181_14840.wl_deferred);
                  ctr = (uu___181_14840.ctr);
                  defer_ok = false;
                  smt_ok = (uu___181_14840.smt_ok);
                  tcenv = (uu___181_14840.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____14847  ->
                      match uu____14847 with
                      | (lb,v1) ->
                          let uu____14852 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____14852 with
                           | USolved wl1 -> ()
                           | uu____14854 -> fail lb v1))) in
            let rec check_ineq uu____14860 =
              match uu____14860 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____14867) -> true
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
                      uu____14878,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____14880,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____14885) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____14889,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____14894 -> false) in
            let uu____14897 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____14903  ->
                      match uu____14903 with
                      | (u,v1) ->
                          let uu____14908 = check_ineq (u, v1) in
                          if uu____14908
                          then true
                          else
                            ((let uu____14911 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____14911
                              then
                                let uu____14912 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____14913 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____14912
                                  uu____14913
                              else ());
                             false))) in
            if uu____14897
            then ()
            else
              ((let uu____14917 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____14917
                then
                  ((let uu____14919 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____14919);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____14925 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____14925))
                else ());
               (let uu____14931 =
                  let uu____14932 =
                    let uu____14935 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____14935) in
                  FStar_Errors.Error uu____14932 in
                raise uu____14931))
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
      let fail uu____14968 =
        match uu____14968 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____14978 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____14978
       then
         let uu____14979 = wl_to_string wl in
         let uu____14980 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____14979 uu____14980
       else ());
      (let g1 =
         let uu____14995 = solve_and_commit env wl fail in
         match uu____14995 with
         | Some [] ->
             let uu___182_15002 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___182_15002.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___182_15002.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___182_15002.FStar_TypeChecker_Env.implicits)
             }
         | uu____15005 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___183_15008 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___183_15008.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___183_15008.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___183_15008.FStar_TypeChecker_Env.implicits)
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
            let uu___184_15034 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___184_15034.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___184_15034.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___184_15034.FStar_TypeChecker_Env.implicits)
            } in
          let uu____15035 =
            let uu____15036 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____15036 in
          if uu____15035
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15042 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____15042
                   then
                     let uu____15043 = FStar_TypeChecker_Env.get_range env in
                     let uu____15044 =
                       let uu____15045 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15045 in
                     FStar_Errors.diag uu____15043 uu____15044
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding] env vc in
                   let uu____15048 = check_trivial vc1 in
                   match uu____15048 with
                   | FStar_TypeChecker_Common.Trivial  -> Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then None
                       else
                         ((let uu____15055 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15055
                           then
                             let uu____15056 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____15057 =
                               let uu____15058 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15058 in
                             FStar_Errors.diag uu____15056 uu____15057
                           else ());
                          (let vcs =
                             let uu____15064 = FStar_Options.use_tactics () in
                             if uu____15064
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)] in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____15078  ->
                                   match uu____15078 with
                                   | (env1,goal) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify]
                                           env1 goal in
                                       let uu____15084 = check_trivial goal1 in
                                       (match uu____15084 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____15086 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____15086
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                                               ();
                                             (let uu____15091 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____15091
                                              then
                                                let uu____15092 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____15093 =
                                                  let uu____15094 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____15095 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____15094 uu____15095 in
                                                FStar_Errors.diag uu____15092
                                                  uu____15093
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
      let uu____15103 = discharge_guard' None env g false in
      match uu____15103 with
      | Some g1 -> g1
      | None  ->
          let uu____15108 =
            let uu____15109 =
              let uu____15112 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____15112) in
            FStar_Errors.Error uu____15109 in
          raise uu____15108
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15119 = discharge_guard' None env g true in
      match uu____15119 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____15131 = FStar_Syntax_Unionfind.find u in
      match uu____15131 with | None  -> true | uu____15133 -> false in
    let rec until_fixpoint acc implicits =
      let uu____15146 = acc in
      match uu____15146 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____15192 = hd1 in
               (match uu____15192 with
                | (uu____15199,env,u,tm,k,r) ->
                    let uu____15205 = unresolved u in
                    if uu____15205
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm in
                       (let uu____15223 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck") in
                        if uu____15223
                        then
                          let uu____15224 =
                            FStar_Syntax_Print.uvar_to_string u in
                          let uu____15225 =
                            FStar_Syntax_Print.term_to_string tm1 in
                          let uu____15226 =
                            FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____15224 uu____15225 uu____15226
                        else ());
                       (let uu____15228 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___185_15232 = env1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___185_15232.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___185_15232.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___185_15232.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___185_15232.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___185_15232.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___185_15232.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___185_15232.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___185_15232.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___185_15232.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___185_15232.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___185_15232.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___185_15232.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___185_15232.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___185_15232.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___185_15232.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___185_15232.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___185_15232.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___185_15232.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___185_15232.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___185_15232.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___185_15232.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___185_15232.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___185_15232.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___185_15232.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___185_15232.FStar_TypeChecker_Env.synth)
                             }) tm1 in
                        match uu____15228 with
                        | (uu____15233,uu____15234,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___186_15237 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___186_15237.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___186_15237.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___186_15237.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____15240 =
                                discharge_guard'
                                  (Some
                                     (fun uu____15244  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____15240 with
                              | Some g3 -> g3
                              | None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
    let uu___187_15259 = g in
    let uu____15260 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___187_15259.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___187_15259.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___187_15259.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____15260
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____15288 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____15288 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15295 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15295
      | (reason,uu____15297,uu____15298,e,t,r)::uu____15302 ->
          let uu____15316 =
            let uu____15317 = FStar_Syntax_Print.term_to_string t in
            let uu____15318 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2
              "Failed to resolve implicit argument of type '%s' introduced in %s"
              uu____15317 uu____15318 in
          FStar_Errors.err r uu____15316
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___188_15325 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___188_15325.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___188_15325.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___188_15325.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15343 = try_teq false env t1 t2 in
        match uu____15343 with
        | None  -> false
        | Some g ->
            let uu____15346 = discharge_guard' None env g false in
            (match uu____15346 with
             | Some uu____15350 -> true
             | None  -> false)