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
            let uu___133_75 = g1 in
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
                      (fun _0_29  -> FStar_Util.Inl _0_29) in
                  Some uu____87 in
                FStar_Syntax_Util.abs uu____78 f uu____80 in
              FStar_All.pipe_left
                (fun _0_30  -> FStar_TypeChecker_Common.NonTrivial _0_30)
                uu____77 in
            {
              FStar_TypeChecker_Env.guard_f = uu____76;
              FStar_TypeChecker_Env.deferred =
                (uu___133_75.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___133_75.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___133_75.FStar_TypeChecker_Env.implicits)
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
          let uu___134_115 = g in
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
              (fun _0_31  -> FStar_TypeChecker_Common.NonTrivial _0_31)
              uu____117 in
          {
            FStar_TypeChecker_Env.guard_f = uu____116;
            FStar_TypeChecker_Env.deferred =
              (uu___134_115.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___134_115.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___134_115.FStar_TypeChecker_Env.implicits)
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
          let uu___135_156 = g in
          let uu____157 =
            let uu____158 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____158 in
          {
            FStar_TypeChecker_Env.guard_f = uu____157;
            FStar_TypeChecker_Env.deferred =
              (uu___135_156.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___135_156.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___135_156.FStar_TypeChecker_Env.implicits)
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
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_TypeChecker_Common.guard_formula
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
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
        let uu____215 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
        {
          FStar_TypeChecker_Env.guard_f = uu____215;
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
                       let uu____260 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____260
                       then f1
                       else FStar_Syntax_Util.mk_forall u (fst b) f1) us bs f in
            let uu___136_262 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___136_262.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___136_262.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___136_262.FStar_TypeChecker_Env.implicits)
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
               let uu____276 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____276
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
            let uu___137_289 = g in
            let uu____290 =
              let uu____291 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____291 in
            {
              FStar_TypeChecker_Env.guard_f = uu____290;
              FStar_TypeChecker_Env.deferred =
                (uu___137_289.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___137_289.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___137_289.FStar_TypeChecker_Env.implicits)
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
        let uv = FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar in
        match binders with
        | [] ->
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k))
                (Some (k.FStar_Syntax_Syntax.n)) r in
            (uv1, uv1)
        | uu____332 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____347 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____347 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                None r in
            let uu____363 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                (Some (k.FStar_Syntax_Syntax.n)) r in
            (uu____363, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____392 = FStar_Syntax_Util.type_u () in
        match uu____392 with
        | (t_type,u) ->
            let uu____397 =
              let uu____400 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____400 t_type in
            (match uu____397 with
             | (tt,uu____402) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of ((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
  FStar_Syntax_Syntax.term)
  | UNIV of (FStar_Syntax_Syntax.universe_uvar* FStar_Syntax_Syntax.universe)
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____423 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
      FStar_Syntax_Syntax.term)
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____449 -> false
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
    match projectee with | Success _0 -> true | uu____529 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____543 -> false
let __proj__Failed__item___0:
  solution -> (FStar_TypeChecker_Common.prob* Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0
type variance =
  | COVARIANT
  | CONTRAVARIANT
  | INVARIANT
let uu___is_COVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____560 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____564 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____568 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___105_585  ->
    match uu___105_585 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____598 =
    let uu____599 = FStar_Syntax_Subst.compress t in
    uu____599.FStar_Syntax_Syntax.n in
  match uu____598 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____616 = FStar_Syntax_Print.uvar_to_string u in
      let uu____620 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____616 uu____620
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____623;
         FStar_Syntax_Syntax.pos = uu____624;
         FStar_Syntax_Syntax.vars = uu____625;_},args)
      ->
      let uu____653 = FStar_Syntax_Print.uvar_to_string u in
      let uu____657 = FStar_Syntax_Print.term_to_string ty in
      let uu____658 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" uu____653 uu____657 uu____658
  | uu____659 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___106_665  ->
      match uu___106_665 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____669 =
            let uu____671 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____672 =
              let uu____674 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____675 =
                let uu____677 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____678 =
                  let uu____680 =
                    let uu____682 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____683 =
                      let uu____685 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____686 =
                        let uu____688 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (fst p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____689 =
                          let uu____691 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____691] in
                        uu____688 :: uu____689 in
                      uu____685 :: uu____686 in
                    uu____682 :: uu____683 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____680 in
                uu____677 :: uu____678 in
              uu____674 :: uu____675 in
            uu____671 :: uu____672 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____669
      | FStar_TypeChecker_Common.CProb p ->
          let uu____696 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____697 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____696
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____697
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___107_703  ->
      match uu___107_703 with
      | UNIV (u,t) ->
          let x =
            let uu____707 = FStar_Options.hide_uvar_nums () in
            if uu____707
            then "?"
            else
              (let uu____709 = FStar_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____709 FStar_Util.string_of_int) in
          let uu____711 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____711
      | TERM ((u,uu____713),t) ->
          let x =
            let uu____718 = FStar_Options.hide_uvar_nums () in
            if uu____718
            then "?"
            else
              (let uu____720 = FStar_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____720 FStar_Util.string_of_int) in
          let uu____724 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____724
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____733 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____733 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____741 =
      let uu____743 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____743
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____741 (FStar_String.concat ", ")
let args_to_string args =
  let uu____761 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____769  ->
            match uu____769 with
            | (x,uu____773) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right uu____761 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____778 =
      let uu____779 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____779 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____778;
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
        let uu___138_792 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___138_792.wl_deferred);
          ctr = (uu___138_792.ctr);
          defer_ok = (uu___138_792.defer_ok);
          smt_ok;
          tcenv = (uu___138_792.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___139_817 = empty_worklist env in
  let uu____818 = FStar_List.map FStar_Pervasives.snd g in
  {
    attempting = uu____818;
    wl_deferred = (uu___139_817.wl_deferred);
    ctr = (uu___139_817.ctr);
    defer_ok = false;
    smt_ok = (uu___139_817.smt_ok);
    tcenv = (uu___139_817.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___140_830 = wl in
        {
          attempting = (uu___140_830.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___140_830.ctr);
          defer_ok = (uu___140_830.defer_ok);
          smt_ok = (uu___140_830.smt_ok);
          tcenv = (uu___140_830.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___141_842 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___141_842.wl_deferred);
        ctr = (uu___141_842.ctr);
        defer_ok = (uu___141_842.defer_ok);
        smt_ok = (uu___141_842.smt_ok);
        tcenv = (uu___141_842.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____853 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____853
         then
           let uu____854 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____854
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___108_858  ->
    match uu___108_858 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___142_874 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___142_874.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___142_874.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___142_874.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___142_874.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___142_874.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___142_874.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___142_874.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___109_895  ->
    match uu___109_895 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_32  -> FStar_TypeChecker_Common.TProb _0_32)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_33  -> FStar_TypeChecker_Common.CProb _0_33)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___110_911  ->
      match uu___110_911 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___111_914  ->
    match uu___111_914 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___112_923  ->
    match uu___112_923 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___113_933  ->
    match uu___113_933 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___114_943  ->
    match uu___114_943 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun uu___115_954  ->
    match uu___115_954 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___116_965  ->
    match uu___116_965 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___117_974  ->
    match uu___117_974 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_34  -> FStar_TypeChecker_Common.TProb _0_34) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_35  -> FStar_TypeChecker_Common.CProb _0_35) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____988 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____988 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____999  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1049 = next_pid () in
  let uu____1050 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1049;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1050;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1097 = next_pid () in
  let uu____1098 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1097;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1098;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1139 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1139;
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
        let uu____1191 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1191
        then
          let uu____1192 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1193 = prob_to_string env d in
          let uu____1194 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1192 uu____1193 uu____1194 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1199 -> failwith "impossible" in
           let uu____1200 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1208 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1209 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1208, uu____1209)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1213 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1214 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1213, uu____1214) in
           match uu____1200 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___118_1223  ->
            match uu___118_1223 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Unionfind.union u u'
                 | uu____1230 -> FStar_Unionfind.change u (Some t))
            | TERM ((u,uu____1233),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar -> uvi Prims.list -> FStar_Syntax_Syntax.term option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___119_1256  ->
           match uu___119_1256 with
           | UNIV uu____1258 -> None
           | TERM ((u,uu____1262),t) ->
               let uu____1266 = FStar_Unionfind.equivalent uv u in
               if uu____1266 then Some t else None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe option FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___120_1285  ->
           match uu___120_1285 with
           | UNIV (u',t) ->
               let uu____1289 = FStar_Unionfind.equivalent u u' in
               if uu____1289 then Some t else None
           | uu____1293 -> None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1300 =
        let uu____1301 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1301 in
      FStar_Syntax_Subst.compress uu____1300
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1308 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1308
let norm_arg env t = let uu____1327 = sn env (fst t) in (uu____1327, (snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1344  ->
              match uu____1344 with
              | (x,imp) ->
                  let uu____1351 =
                    let uu___143_1352 = x in
                    let uu____1353 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___143_1352.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___143_1352.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1353
                    } in
                  (uu____1351, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1368 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1368
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1371 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1371
        | uu____1373 -> u2 in
      let uu____1374 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1374
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1481 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____1481 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1493;
               FStar_Syntax_Syntax.pos = uu____1494;
               FStar_Syntax_Syntax.vars = uu____1495;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1516 =
                 let uu____1517 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1518 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1517
                   uu____1518 in
               failwith uu____1516)
    | FStar_Syntax_Syntax.Tm_uinst uu____1528 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1555 =
             let uu____1556 = FStar_Syntax_Subst.compress t1' in
             uu____1556.FStar_Syntax_Syntax.n in
           match uu____1555 with
           | FStar_Syntax_Syntax.Tm_refine uu____1568 -> aux true t1'
           | uu____1573 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1585 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1608 =
             let uu____1609 = FStar_Syntax_Subst.compress t1' in
             uu____1609.FStar_Syntax_Syntax.n in
           match uu____1608 with
           | FStar_Syntax_Syntax.Tm_refine uu____1621 -> aux true t1'
           | uu____1626 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_app uu____1638 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1670 =
             let uu____1671 = FStar_Syntax_Subst.compress t1' in
             uu____1671.FStar_Syntax_Syntax.n in
           match uu____1670 with
           | FStar_Syntax_Syntax.Tm_refine uu____1683 -> aux true t1'
           | uu____1688 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_type uu____1700 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_constant uu____1712 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_name uu____1724 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1736 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1748 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_abs uu____1767 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1793 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_let uu____1813 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_match uu____1832 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_meta uu____1859 ->
        let uu____1864 =
          let uu____1865 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1866 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1865
            uu____1866 in
        failwith uu____1864
    | FStar_Syntax_Syntax.Tm_ascribed uu____1876 ->
        let uu____1894 =
          let uu____1895 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1896 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1895
            uu____1896 in
        failwith uu____1894
    | FStar_Syntax_Syntax.Tm_delayed uu____1906 ->
        let uu____1927 =
          let uu____1928 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1929 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1928
            uu____1929 in
        failwith uu____1927
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1939 =
          let uu____1940 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1941 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1940
            uu____1941 in
        failwith uu____1939 in
  let uu____1951 = whnf env t1 in aux false uu____1951
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1960 =
        let uu____1970 = empty_worklist env in
        base_and_refinement env uu____1970 t in
      FStar_All.pipe_right uu____1960 FStar_Pervasives.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____1994 = FStar_Syntax_Syntax.null_bv t in
    (uu____1994, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____2014 = base_and_refinement env wl t in
  match uu____2014 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
let force_refinement uu____2073 =
  match uu____2073 with
  | (t_base,refopt) ->
      let uu____2087 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base in
      (match uu____2087 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___121_2111  ->
      match uu___121_2111 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2115 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2116 =
            let uu____2117 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____2117 in
          let uu____2118 =
            let uu____2119 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____2119 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2115 uu____2116
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2118
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2123 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2124 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____2125 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2123 uu____2124
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2125
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2129 =
      let uu____2131 =
        let uu____2133 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2143  ->
                  match uu____2143 with | (uu____2147,uu____2148,x) -> x)) in
        FStar_List.append wl.attempting uu____2133 in
      FStar_List.map (wl_prob_to_string wl) uu____2131 in
    FStar_All.pipe_right uu____2129 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2166 =
          let uu____2176 =
            let uu____2177 = FStar_Syntax_Subst.compress k in
            uu____2177.FStar_Syntax_Syntax.n in
          match uu____2176 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2218 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2218)
              else
                (let uu____2232 = FStar_Syntax_Util.abs_formals t in
                 match uu____2232 with
                 | (ys',t1,uu____2253) ->
                     let uu____2266 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2266))
          | uu____2287 ->
              let uu____2288 =
                let uu____2294 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____2294) in
              ((ys, t), uu____2288) in
        match uu____2166 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2349 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2349 c in
               let uu____2351 =
                 let uu____2358 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_36  -> FStar_Util.Inl _0_36) in
                 FStar_All.pipe_right uu____2358 (fun _0_37  -> Some _0_37) in
               FStar_Syntax_Util.abs ys1 t1 uu____2351)
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
            let uu____2409 = p_guard prob in
            match uu____2409 with
            | (uu____2412,uv) ->
                ((let uu____2415 =
                    let uu____2416 = FStar_Syntax_Subst.compress uv in
                    uu____2416.FStar_Syntax_Syntax.n in
                  match uu____2415 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2436 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2436
                        then
                          let uu____2437 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2438 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2439 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2437
                            uu____2438 uu____2439
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2443 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___144_2446 = wl in
                  {
                    attempting = (uu___144_2446.attempting);
                    wl_deferred = (uu___144_2446.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___144_2446.defer_ok);
                    smt_ok = (uu___144_2446.smt_ok);
                    tcenv = (uu___144_2446.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2459 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2459
         then
           let uu____2460 = FStar_Util.string_of_int pid in
           let uu____2461 =
             let uu____2462 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2462 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2460 uu____2461
         else ());
        commit sol;
        (let uu___145_2467 = wl in
         {
           attempting = (uu___145_2467.attempting);
           wl_deferred = (uu___145_2467.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___145_2467.defer_ok);
           smt_ok = (uu___145_2467.smt_ok);
           tcenv = (uu___145_2467.tcenv)
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
            | (uu____2496,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2504 = FStar_Syntax_Util.mk_conj t1 f in
                Some uu____2504 in
          (let uu____2510 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2510
           then
             let uu____2511 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2512 =
               let uu____2513 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2513 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2511 uu____2512
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2538 =
    let uu____2542 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2542 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2538
    (FStar_Util.for_some
       (fun uu____2563  ->
          match uu____2563 with
          | (uv,uu____2571) -> FStar_Unionfind.equivalent uv (fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2615 = occurs wl uk t in Prims.op_Negation uu____2615 in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2620 =
         let uu____2621 = FStar_Syntax_Print.uvar_to_string (fst uk) in
         let uu____2625 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2621 uu____2625 in
       Some uu____2620) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2673 = occurs_check env wl uk t in
  match uu____2673 with
  | (occurs_ok,msg) ->
      let uu____2690 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2690, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2754 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2778  ->
            fun uu____2779  ->
              match (uu____2778, uu____2779) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2822 =
                    let uu____2823 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2823 in
                  if uu____2822
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2837 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2837
                     then
                       let uu____2844 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____2844)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2754 with | (isect,uu____2866) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2915  ->
          fun uu____2916  ->
            match (uu____2915, uu____2916) with
            | ((a,uu____2926),(b,uu____2928)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2972 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2978  ->
                match uu____2978 with
                | (b,uu____2982) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____2972 then None else Some (a, (snd hd1))
  | uu____2991 -> None
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
            let uu____3034 = pat_var_opt env seen hd1 in
            (match uu____3034 with
             | None  ->
                 ((let uu____3042 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____3042
                   then
                     let uu____3043 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____3043
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3055 =
      let uu____3056 = FStar_Syntax_Subst.compress t in
      uu____3056.FStar_Syntax_Syntax.n in
    match uu____3055 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3059 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3068;
           FStar_Syntax_Syntax.tk = uu____3069;
           FStar_Syntax_Syntax.pos = uu____3070;
           FStar_Syntax_Syntax.vars = uu____3071;_},uu____3072)
        -> true
    | uu____3095 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3157;
         FStar_Syntax_Syntax.pos = uu____3158;
         FStar_Syntax_Syntax.vars = uu____3159;_},args)
      -> (t, uv, k, args)
  | uu____3200 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____3254 = destruct_flex_t t in
  match uu____3254 with
  | (t1,uv,k,args) ->
      let uu____3322 = pat_vars env [] args in
      (match uu____3322 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3378 -> ((t1, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth option*
  FStar_Syntax_Syntax.delta_depth option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3426 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth option* FStar_Syntax_Syntax.delta_depth
      option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3449 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3453 -> false
let head_match: match_result -> match_result =
  fun uu___122_3456  ->
    match uu___122_3456 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3465 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3478 ->
          let uu____3479 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3479 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3489 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3503 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3509 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> None
      | FStar_Syntax_Syntax.Tm_bvar uu____3531 -> None
      | FStar_Syntax_Syntax.Tm_name uu____3532 -> None
      | FStar_Syntax_Syntax.Tm_uvar uu____3533 -> None
      | FStar_Syntax_Syntax.Tm_let uu____3542 -> None
      | FStar_Syntax_Syntax.Tm_match uu____3550 -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3567) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3573,uu____3574) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3604) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3619;
             FStar_Syntax_Syntax.index = uu____3620;
             FStar_Syntax_Syntax.sort = t2;_},uu____3622)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3629 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3630 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3631 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3639 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3655 = fv_delta_depth env fv in Some uu____3655
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
            let uu____3674 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3674
            then FullMatch
            else
              (let uu____3676 =
                 let uu____3681 =
                   let uu____3683 = fv_delta_depth env f in Some uu____3683 in
                 let uu____3684 =
                   let uu____3686 = fv_delta_depth env g in Some uu____3686 in
                 (uu____3681, uu____3684) in
               MisMatch uu____3676)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3690),FStar_Syntax_Syntax.Tm_uinst (g,uu____3692)) ->
            let uu____3701 = head_matches env f g in
            FStar_All.pipe_right uu____3701 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3708),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3710)) ->
            let uu____3735 = FStar_Unionfind.equivalent uv uv' in
            if uu____3735 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3743),FStar_Syntax_Syntax.Tm_refine (y,uu____3745)) ->
            let uu____3754 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3754 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3756),uu____3757) ->
            let uu____3762 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3762 head_match
        | (uu____3763,FStar_Syntax_Syntax.Tm_refine (x,uu____3765)) ->
            let uu____3770 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3770 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3771,FStar_Syntax_Syntax.Tm_type
           uu____3772) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3773,FStar_Syntax_Syntax.Tm_arrow uu____3774) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3790),FStar_Syntax_Syntax.Tm_app (head',uu____3792))
            ->
            let uu____3821 = head_matches env head1 head' in
            FStar_All.pipe_right uu____3821 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3823),uu____3824) ->
            let uu____3839 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____3839 head_match
        | (uu____3840,FStar_Syntax_Syntax.Tm_app (head1,uu____3842)) ->
            let uu____3857 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____3857 head_match
        | uu____3858 ->
            let uu____3861 =
              let uu____3866 = delta_depth_of_term env t11 in
              let uu____3868 = delta_depth_of_term env t21 in
              (uu____3866, uu____3868) in
            MisMatch uu____3861
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3904 = FStar_Syntax_Util.head_and_args t in
    match uu____3904 with
    | (head1,uu____3916) ->
        let uu____3931 =
          let uu____3932 = FStar_Syntax_Util.un_uinst head1 in
          uu____3932.FStar_Syntax_Syntax.n in
        (match uu____3931 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3937 =
               let uu____3938 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____3938 FStar_Option.isSome in
             if uu____3937
             then
               let uu____3952 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____3952 (fun _0_38  -> Some _0_38)
             else None
         | uu____3955 -> None) in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None)) in
  let fail r = (r, None) in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21 in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),uu____4023) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4033 =
             let uu____4038 = maybe_inline t11 in
             let uu____4040 = maybe_inline t21 in (uu____4038, uu____4040) in
           match uu____4033 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (uu____4061,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4071 =
             let uu____4076 = maybe_inline t11 in
             let uu____4078 = maybe_inline t21 in (uu____4076, uu____4078) in
           match uu____4071 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____4103 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____4103 with
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
        let uu____4118 =
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
             let uu____4126 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____4126)) in
        (match uu____4118 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4134 -> fail r
    | uu____4139 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4164 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4194 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4209 = FStar_Syntax_Util.type_u () in
      match uu____4209 with
      | (t,uu____4213) ->
          let uu____4214 = new_uvar r binders t in fst uu____4214
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4223 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____4223 FStar_Pervasives.fst
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
        let uu____4265 = head_matches env t1 t' in
        match uu____4265 with
        | MisMatch uu____4266 -> false
        | uu____4271 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4331,imp),T (t2,uu____4334)) -> (t2, imp)
                     | uu____4351 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4391  ->
                    match uu____4391 with
                    | (t2,uu____4399) ->
                        (None, INVARIANT, (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let fail uu____4432 = failwith "Bad reconstruction" in
          let uu____4433 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____4433 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4486))::tcs2) ->
                       aux
                         (((let uu___146_4508 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_4508.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_4508.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4518 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___123_4549 =
                 match uu___123_4549 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4612 = decompose1 [] bs1 in
               (rebuild, matches, uu____4612))
      | uu____4640 ->
          let rebuild uu___124_4645 =
            match uu___124_4645 with
            | [] -> t1
            | uu____4647 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___125_4666  ->
    match uu___125_4666 with
    | T (t,uu____4668) -> t
    | uu____4677 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___126_4680  ->
    match uu___126_4680 with
    | T (t,uu____4682) -> FStar_Syntax_Syntax.as_arg t
    | uu____4691 -> failwith "Impossible"
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
              | (uu____4760,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4779 = new_uvar r scope1 k in
                  (match uu____4779 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4791 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args)) None r in
                       let uu____4806 =
                         let uu____4807 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_39  ->
                              FStar_TypeChecker_Common.TProb _0_39)
                           uu____4807 in
                       ((T (gi_xs, mk_kind)), uu____4806))
              | (uu____4816,uu____4817,C uu____4818) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4905 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4916;
                         FStar_Syntax_Syntax.pos = uu____4917;
                         FStar_Syntax_Syntax.vars = uu____4918;_})
                        ->
                        let uu____4933 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4933 with
                         | (T (gi_xs,uu____4949),prob) ->
                             let uu____4959 =
                               let uu____4960 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_40  -> C _0_40)
                                 uu____4960 in
                             (uu____4959, [prob])
                         | uu____4962 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4972;
                         FStar_Syntax_Syntax.pos = uu____4973;
                         FStar_Syntax_Syntax.vars = uu____4974;_})
                        ->
                        let uu____4989 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4989 with
                         | (T (gi_xs,uu____5005),prob) ->
                             let uu____5015 =
                               let uu____5016 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_41  -> C _0_41)
                                 uu____5016 in
                             (uu____5015, [prob])
                         | uu____5018 -> failwith "impossible")
                    | (uu____5024,uu____5025,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____5027;
                         FStar_Syntax_Syntax.pos = uu____5028;
                         FStar_Syntax_Syntax.vars = uu____5029;_})
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
                        let uu____5103 =
                          let uu____5108 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____5108 FStar_List.unzip in
                        (match uu____5103 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5137 =
                                 let uu____5138 =
                                   let uu____5141 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____5141 un_T in
                                 let uu____5142 =
                                   let uu____5148 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____5148
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5138;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5142;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5137 in
                             ((C gi_xs), sub_probs))
                    | uu____5153 ->
                        let uu____5160 = sub_prob scope1 args q in
                        (match uu____5160 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____4905 with
                   | (tc,probs) ->
                       let uu____5178 =
                         match q with
                         | (Some b,uu____5204,uu____5205) ->
                             let uu____5213 =
                               let uu____5217 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____5217 :: args in
                             ((Some b), (b :: scope1), uu____5213)
                         | uu____5235 -> (None, scope1, args) in
                       (match uu____5178 with
                        | (bopt,scope2,args1) ->
                            let uu____5278 = aux scope2 args1 qs2 in
                            (match uu____5278 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____5299 =
                                         let uu____5301 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         f :: uu____5301 in
                                       FStar_Syntax_Util.mk_conj_l uu____5299
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (fst b).FStar_Syntax_Syntax.sort in
                                       let uu____5314 =
                                         let uu____5316 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (fst b) f in
                                         let uu____5317 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         uu____5316 :: uu____5317 in
                                       FStar_Syntax_Util.mk_conj_l uu____5314 in
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
  let uu___147_5370 = p in
  let uu____5373 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____5374 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___147_5370.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5373;
    FStar_TypeChecker_Common.relation =
      (uu___147_5370.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5374;
    FStar_TypeChecker_Common.element =
      (uu___147_5370.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___147_5370.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___147_5370.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___147_5370.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___147_5370.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___147_5370.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5384 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____5384
            (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
      | FStar_TypeChecker_Common.CProb uu____5389 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5403 = compress_prob wl pr in
        FStar_All.pipe_right uu____5403 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5409 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____5409 with
           | (lh,uu____5422) ->
               let uu____5437 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____5437 with
                | (rh,uu____5450) ->
                    let uu____5465 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5474,FStar_Syntax_Syntax.Tm_uvar uu____5475)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5494,uu____5495)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5506,FStar_Syntax_Syntax.Tm_uvar uu____5507)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5518,uu____5519)
                          ->
                          let uu____5528 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5528 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5568 ->
                                    let rank =
                                      let uu____5575 = is_top_level_prob prob in
                                      if uu____5575
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5577 =
                                      let uu___148_5580 = tp in
                                      let uu____5583 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___148_5580.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___148_5580.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___148_5580.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5583;
                                        FStar_TypeChecker_Common.element =
                                          (uu___148_5580.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___148_5580.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___148_5580.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___148_5580.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___148_5580.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___148_5580.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5577)))
                      | (uu____5593,FStar_Syntax_Syntax.Tm_uvar uu____5594)
                          ->
                          let uu____5603 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5603 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5643 ->
                                    let uu____5649 =
                                      let uu___149_5654 = tp in
                                      let uu____5657 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_5654.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5657;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_5654.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___149_5654.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_5654.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_5654.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_5654.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_5654.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_5654.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_5654.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5649)))
                      | (uu____5673,uu____5674) -> (rigid_rigid, tp) in
                    (match uu____5465 with
                     | (rank,tp1) ->
                         let uu____5685 =
                           FStar_All.pipe_right
                             (let uu___150_5688 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___150_5688.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___150_5688.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___150_5688.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___150_5688.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___150_5688.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___150_5688.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___150_5688.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___150_5688.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___150_5688.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_43  ->
                                FStar_TypeChecker_Common.TProb _0_43) in
                         (rank, uu____5685))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5694 =
            FStar_All.pipe_right
              (let uu___151_5697 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___151_5697.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___151_5697.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___151_5697.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___151_5697.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___151_5697.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___151_5697.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___151_5697.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___151_5697.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___151_5697.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) in
          (rigid_rigid, uu____5694)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob option* FStar_TypeChecker_Common.prob
      Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____5729 probs =
      match uu____5729 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5759 = rank wl hd1 in
               (match uu____5759 with
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
    match projectee with | UDeferred _0 -> true | uu____5824 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5836 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5848 -> false
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
                        let uu____5885 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____5885 with
                        | (k,uu____5889) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Unionfind.equivalent v1 v2
                             | uu____5894 -> false)))
            | uu____5895 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____5938 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____5938 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5941 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____5947 =
                     let uu____5948 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____5949 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5948
                       uu____5949 in
                   UFailed uu____5947)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5965 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5965 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5983 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5983 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____5986 ->
                let uu____5989 =
                  let uu____5990 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____5991 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5990
                    uu____5991 msg in
                UFailed uu____5989 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____5992,uu____5993) ->
              let uu____5994 =
                let uu____5995 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5996 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5995 uu____5996 in
              failwith uu____5994
          | (FStar_Syntax_Syntax.U_unknown ,uu____5997) ->
              let uu____5998 =
                let uu____5999 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6000 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5999 uu____6000 in
              failwith uu____5998
          | (uu____6001,FStar_Syntax_Syntax.U_bvar uu____6002) ->
              let uu____6003 =
                let uu____6004 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6005 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6004 uu____6005 in
              failwith uu____6003
          | (uu____6006,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____6007 =
                let uu____6008 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6009 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6008 uu____6009 in
              failwith uu____6007
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____6021 = FStar_Unionfind.equivalent v1 v2 in
              if uu____6021
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____6032 = occurs_univ v1 u3 in
              if uu____6032
              then
                let uu____6033 =
                  let uu____6034 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6035 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6034 uu____6035 in
                try_umax_components u11 u21 uu____6033
              else
                (let uu____6037 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6037)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____6045 = occurs_univ v1 u3 in
              if uu____6045
              then
                let uu____6046 =
                  let uu____6047 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6048 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6047 uu____6048 in
                try_umax_components u11 u21 uu____6046
              else
                (let uu____6050 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6050)
          | (FStar_Syntax_Syntax.U_max uu____6053,uu____6054) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6059 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6059
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____6061,FStar_Syntax_Syntax.U_max uu____6062) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6067 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6067
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6069,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6070,FStar_Syntax_Syntax.U_name
             uu____6071) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6072) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6073) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6074,FStar_Syntax_Syntax.U_succ
             uu____6075) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6076,FStar_Syntax_Syntax.U_zero
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
  let uu____6138 = bc1 in
  match uu____6138 with
  | (bs1,mk_cod1) ->
      let uu____6163 = bc2 in
      (match uu____6163 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6210 = FStar_Util.first_N n1 bs in
             match uu____6210 with
             | (bs3,rest) ->
                 let uu____6224 = mk_cod rest in (bs3, uu____6224) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____6242 =
               let uu____6246 = mk_cod1 [] in (bs1, uu____6246) in
             let uu____6248 =
               let uu____6252 = mk_cod2 [] in (bs2, uu____6252) in
             (uu____6242, uu____6248)
           else
             if l1 > l2
             then
               (let uu____6274 = curry l2 bs1 mk_cod1 in
                let uu____6281 =
                  let uu____6285 = mk_cod2 [] in (bs2, uu____6285) in
                (uu____6274, uu____6281))
             else
               (let uu____6294 =
                  let uu____6298 = mk_cod1 [] in (bs1, uu____6298) in
                let uu____6300 = curry l1 bs2 mk_cod2 in
                (uu____6294, uu____6300)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6404 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____6404
       then
         let uu____6405 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6405
       else ());
      (let uu____6407 = next_prob probs in
       match uu____6407 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___152_6420 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___152_6420.wl_deferred);
               ctr = (uu___152_6420.ctr);
               defer_ok = (uu___152_6420.defer_ok);
               smt_ok = (uu___152_6420.smt_ok);
               tcenv = (uu___152_6420.tcenv)
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
                  let uu____6427 = solve_flex_rigid_join env tp probs1 in
                  (match uu____6427 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6431 = solve_rigid_flex_meet env tp probs1 in
                     match uu____6431 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____6435,uu____6436) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6445 ->
                let uu____6450 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6478  ->
                          match uu____6478 with
                          | (c,uu____6483,uu____6484) -> c < probs.ctr)) in
                (match uu____6450 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6506 =
                            FStar_List.map
                              (fun uu____6512  ->
                                 match uu____6512 with
                                 | (uu____6518,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____6506
                      | uu____6521 ->
                          let uu____6526 =
                            let uu___153_6527 = probs in
                            let uu____6528 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6537  ->
                                      match uu____6537 with
                                      | (uu____6541,uu____6542,y) -> y)) in
                            {
                              attempting = uu____6528;
                              wl_deferred = rest;
                              ctr = (uu___153_6527.ctr);
                              defer_ok = (uu___153_6527.defer_ok);
                              smt_ok = (uu___153_6527.smt_ok);
                              tcenv = (uu___153_6527.tcenv)
                            } in
                          solve env uu____6526))))
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
            let uu____6549 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____6549 with
            | USolved wl1 ->
                let uu____6551 = solve_prob orig None [] wl1 in
                solve env uu____6551
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
                  let uu____6585 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6585 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6588 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6596;
                  FStar_Syntax_Syntax.pos = uu____6597;
                  FStar_Syntax_Syntax.vars = uu____6598;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6601;
                  FStar_Syntax_Syntax.pos = uu____6602;
                  FStar_Syntax_Syntax.vars = uu____6603;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6615,uu____6616) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6621,FStar_Syntax_Syntax.Tm_uinst uu____6622) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6627 -> USolved wl
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
            ((let uu____6635 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6635
              then
                let uu____6636 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6636 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6644 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6644
         then
           let uu____6645 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6645
         else ());
        (let uu____6647 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6647 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6689 = head_matches_delta env () t1 t2 in
               match uu____6689 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6711 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6737 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6746 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____6747 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____6746, uu____6747)
                          | None  ->
                              let uu____6750 = FStar_Syntax_Subst.compress t1 in
                              let uu____6751 = FStar_Syntax_Subst.compress t2 in
                              (uu____6750, uu____6751) in
                        (match uu____6737 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6773 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_45  ->
                                    FStar_TypeChecker_Common.TProb _0_45)
                                 uu____6773 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6796 =
                                    let uu____6802 =
                                      let uu____6805 =
                                        let uu____6808 =
                                          let uu____6809 =
                                            let uu____6814 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____6814) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6809 in
                                        FStar_Syntax_Syntax.mk uu____6808 in
                                      uu____6805 None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____6827 =
                                      let uu____6829 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____6829] in
                                    (uu____6802, uu____6827) in
                                  Some uu____6796
                              | (uu____6838,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6840)) ->
                                  let uu____6845 =
                                    let uu____6849 =
                                      let uu____6851 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____6851] in
                                    (t11, uu____6849) in
                                  Some uu____6845
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6857),uu____6858) ->
                                  let uu____6863 =
                                    let uu____6867 =
                                      let uu____6869 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____6869] in
                                    (t21, uu____6867) in
                                  Some uu____6863
                              | uu____6874 ->
                                  let uu____6877 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____6877 with
                                   | (head1,uu____6892) ->
                                       let uu____6907 =
                                         let uu____6908 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____6908.FStar_Syntax_Syntax.n in
                                       (match uu____6907 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6915;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6917;_}
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
                                        | uu____6926 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6935) ->
                  let uu____6948 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___127_6957  ->
                            match uu___127_6957 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6962 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____6962 with
                                      | (u',uu____6973) ->
                                          let uu____6988 =
                                            let uu____6989 = whnf env u' in
                                            uu____6989.FStar_Syntax_Syntax.n in
                                          (match uu____6988 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____6993) ->
                                               FStar_Unionfind.equivalent uv
                                                 uv'
                                           | uu____7009 -> false))
                                 | uu____7010 -> false)
                            | uu____7012 -> false)) in
                  (match uu____6948 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____7033 tps =
                         match uu____7033 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7060 =
                                    let uu____7065 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____7065 in
                                  (match uu____7060 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____7084 -> None) in
                       let uu____7089 =
                         let uu____7094 =
                           let uu____7098 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____7098, []) in
                         make_lower_bound uu____7094 lower_bounds in
                       (match uu____7089 with
                        | None  ->
                            ((let uu____7105 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7105
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
                            ((let uu____7118 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7118
                              then
                                let wl' =
                                  let uu___154_7120 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___154_7120.wl_deferred);
                                    ctr = (uu___154_7120.ctr);
                                    defer_ok = (uu___154_7120.defer_ok);
                                    smt_ok = (uu___154_7120.smt_ok);
                                    tcenv = (uu___154_7120.tcenv)
                                  } in
                                let uu____7121 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7121
                              else ());
                             (let uu____7123 =
                                solve_t env eq_prob
                                  (let uu___155_7124 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___155_7124.wl_deferred);
                                     ctr = (uu___155_7124.ctr);
                                     defer_ok = (uu___155_7124.defer_ok);
                                     smt_ok = (uu___155_7124.smt_ok);
                                     tcenv = (uu___155_7124.tcenv)
                                   }) in
                              match uu____7123 with
                              | Success uu____7126 ->
                                  let wl1 =
                                    let uu___156_7128 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___156_7128.wl_deferred);
                                      ctr = (uu___156_7128.ctr);
                                      defer_ok = (uu___156_7128.defer_ok);
                                      smt_ok = (uu___156_7128.smt_ok);
                                      tcenv = (uu___156_7128.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1 in
                                  let uu____7130 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds in
                                  Some wl2
                              | uu____7133 -> None))))
              | uu____7134 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7141 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____7141
         then
           let uu____7142 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7142
         else ());
        (let uu____7144 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____7144 with
         | (u,args) ->
             let uu____7171 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____7171 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____7202 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____7202 with
                    | (h1,args1) ->
                        let uu____7230 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____7230 with
                         | (h2,uu____7243) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7262 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____7262
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7275 =
                                          let uu____7277 =
                                            let uu____7278 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_46  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_46) uu____7278 in
                                          [uu____7277] in
                                        Some uu____7275))
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
                                       (let uu____7300 =
                                          let uu____7302 =
                                            let uu____7303 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_47  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_47) uu____7303 in
                                          [uu____7302] in
                                        Some uu____7300))
                                  else None
                              | uu____7311 -> None)) in
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
                             let uu____7377 =
                               let uu____7383 =
                                 let uu____7386 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____7386 in
                               (uu____7383, m1) in
                             Some uu____7377)
                    | (uu____7395,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7397)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7429),uu____7430) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____7461 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7495) ->
                       let uu____7508 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___128_7517  ->
                                 match uu___128_7517 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____7522 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____7522 with
                                           | (u',uu____7533) ->
                                               let uu____7548 =
                                                 let uu____7549 = whnf env u' in
                                                 uu____7549.FStar_Syntax_Syntax.n in
                                               (match uu____7548 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7553) ->
                                                    FStar_Unionfind.equivalent
                                                      uv uv'
                                                | uu____7569 -> false))
                                      | uu____7570 -> false)
                                 | uu____7572 -> false)) in
                       (match uu____7508 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7597 tps =
                              match uu____7597 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7638 =
                                         let uu____7645 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7645 in
                                       (match uu____7638 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7680 -> None) in
                            let uu____7687 =
                              let uu____7694 =
                                let uu____7700 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7700, []) in
                              make_upper_bound uu____7694 upper_bounds in
                            (match uu____7687 with
                             | None  ->
                                 ((let uu____7709 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7709
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
                                 ((let uu____7728 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7728
                                   then
                                     let wl' =
                                       let uu___157_7730 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___157_7730.wl_deferred);
                                         ctr = (uu___157_7730.ctr);
                                         defer_ok = (uu___157_7730.defer_ok);
                                         smt_ok = (uu___157_7730.smt_ok);
                                         tcenv = (uu___157_7730.tcenv)
                                       } in
                                     let uu____7731 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7731
                                   else ());
                                  (let uu____7733 =
                                     solve_t env eq_prob
                                       (let uu___158_7734 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___158_7734.wl_deferred);
                                          ctr = (uu___158_7734.ctr);
                                          defer_ok = (uu___158_7734.defer_ok);
                                          smt_ok = (uu___158_7734.smt_ok);
                                          tcenv = (uu___158_7734.tcenv)
                                        }) in
                                   match uu____7733 with
                                   | Success uu____7736 ->
                                       let wl1 =
                                         let uu___159_7738 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___159_7738.wl_deferred);
                                           ctr = (uu___159_7738.ctr);
                                           defer_ok =
                                             (uu___159_7738.defer_ok);
                                           smt_ok = (uu___159_7738.smt_ok);
                                           tcenv = (uu___159_7738.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1 in
                                       let uu____7740 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds in
                                       Some wl2
                                   | uu____7743 -> None))))
                   | uu____7744 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____7809 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____7809
                      then
                        let uu____7810 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7810
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___160_7842 = hd1 in
                      let uu____7843 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___160_7842.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___160_7842.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7843
                      } in
                    let hd21 =
                      let uu___161_7847 = hd2 in
                      let uu____7848 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_7847.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_7847.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7848
                      } in
                    let prob =
                      let uu____7852 =
                        let uu____7855 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7855 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_48  -> FStar_TypeChecker_Common.TProb _0_48)
                        uu____7852 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____7863 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7863 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____7866 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____7866 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7884 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives.fst in
                           let uu____7887 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____7884 uu____7887 in
                         ((let uu____7893 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____7893
                           then
                             let uu____7894 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____7895 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7894 uu____7895
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7910 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____7916 = aux scope env [] bs1 bs2 in
              match uu____7916 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7932 = compress_tprob wl problem in
        solve_t' env uu____7932 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7965 = head_matches_delta env1 wl1 t1 t2 in
          match uu____7965 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7982,uu____7983) ->
                   let may_relate head3 =
                     let uu____7998 =
                       let uu____7999 = FStar_Syntax_Util.un_uinst head3 in
                       uu____7999.FStar_Syntax_Syntax.n in
                     match uu____7998 with
                     | FStar_Syntax_Syntax.Tm_name uu____8002 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____8003 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____8020 -> false in
                   let uu____8021 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____8021
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
                                let uu____8038 =
                                  let uu____8039 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____8039 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____8038 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____8041 = solve_prob orig (Some guard) [] wl1 in
                     solve env1 uu____8041
                   else giveup env1 "head mismatch" orig
               | (uu____8043,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___162_8051 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___162_8051.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___162_8051.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___162_8051.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___162_8051.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___162_8051.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___162_8051.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___162_8051.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___162_8051.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____8052,None ) ->
                   ((let uu____8059 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8059
                     then
                       let uu____8060 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____8061 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____8062 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____8063 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____8060
                         uu____8061 uu____8062 uu____8063
                     else ());
                    (let uu____8065 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____8065 with
                     | (head11,args1) ->
                         let uu____8091 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____8091 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8131 =
                                  let uu____8132 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____8133 = args_to_string args1 in
                                  let uu____8134 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____8135 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8132 uu____8133 uu____8134
                                    uu____8135 in
                                giveup env1 uu____8131 orig
                              else
                                (let uu____8137 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8140 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____8140 = FStar_Syntax_Util.Equal) in
                                 if uu____8137
                                 then
                                   let uu____8141 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____8141 with
                                   | USolved wl2 ->
                                       let uu____8143 =
                                         solve_prob orig None [] wl2 in
                                       solve env1 uu____8143
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8147 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____8147 with
                                    | (base1,refinement1) ->
                                        let uu____8173 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____8173 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____8227 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____8227 with
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
                                                           (fun uu____8237 
                                                              ->
                                                              fun uu____8238 
                                                                ->
                                                                match 
                                                                  (uu____8237,
                                                                    uu____8238)
                                                                with
                                                                | ((a,uu____8248),
                                                                   (a',uu____8250))
                                                                    ->
                                                                    let uu____8255
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
                                                                    _0_49  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_49)
                                                                    uu____8255)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____8261 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8261 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8265 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___163_8298 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___163_8298.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___163_8298.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___163_8298.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___163_8298.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___163_8298.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___163_8298.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___163_8298.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___163_8298.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____8318 = p in
          match uu____8318 with
          | (((u,k),xs,c),ps,(h,uu____8329,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8378 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____8378 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8392 = h gs_xs in
                     let uu____8393 =
                       let uu____8400 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_50  -> FStar_Util.Inl _0_50) in
                       FStar_All.pipe_right uu____8400
                         (fun _0_51  -> Some _0_51) in
                     FStar_Syntax_Util.abs xs1 uu____8392 uu____8393 in
                   ((let uu____8431 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8431
                     then
                       let uu____8432 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____8433 = FStar_Syntax_Print.comp_to_string c in
                       let uu____8434 = FStar_Syntax_Print.term_to_string im in
                       let uu____8435 = FStar_Syntax_Print.tag_of_term im in
                       let uu____8436 =
                         let uu____8437 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____8437
                           (FStar_String.concat ", ") in
                       let uu____8440 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8432 uu____8433 uu____8434 uu____8435
                         uu____8436 uu____8440
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___129_8458 =
          match uu___129_8458 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____8487 = p in
          match uu____8487 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8545 = FStar_List.nth ps i in
              (match uu____8545 with
               | (pi,uu____8548) ->
                   let uu____8553 = FStar_List.nth xs i in
                   (match uu____8553 with
                    | (xi,uu____8560) ->
                        let rec gs k =
                          let uu____8569 = FStar_Syntax_Util.arrow_formals k in
                          match uu____8569 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8621)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8629 = new_uvar r xs k_a in
                                    (match uu____8629 with
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
                                         let uu____8648 = aux subst2 tl1 in
                                         (match uu____8648 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8663 =
                                                let uu____8665 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8665 :: gi_xs' in
                                              let uu____8666 =
                                                let uu____8668 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8668 :: gi_ps' in
                                              (uu____8663, uu____8666))) in
                              aux [] bs in
                        let uu____8671 =
                          let uu____8672 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8672 in
                        if uu____8671
                        then None
                        else
                          (let uu____8675 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8675 with
                           | (g_xs,uu____8682) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8689 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r in
                                 let uu____8694 =
                                   let uu____8701 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_52  -> FStar_Util.Inl _0_52) in
                                   FStar_All.pipe_right uu____8701
                                     (fun _0_53  -> Some _0_53) in
                                 FStar_Syntax_Util.abs xs uu____8689
                                   uu____8694 in
                               let sub1 =
                                 let uu____8732 =
                                   let uu____8735 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let uu____8742 =
                                     let uu____8745 =
                                       FStar_List.map
                                         (fun uu____8751  ->
                                            match uu____8751 with
                                            | (uu____8756,uu____8757,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____8745 in
                                   mk_problem (p_scope orig) orig uu____8735
                                     (p_rel orig) uu____8742 None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_54  ->
                                      FStar_TypeChecker_Common.TProb _0_54)
                                   uu____8732 in
                               ((let uu____8767 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____8767
                                 then
                                   let uu____8768 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____8769 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8768 uu____8769
                                 else ());
                                (let wl2 =
                                   let uu____8772 =
                                     let uu____8774 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives.fst (p_guard sub1) in
                                     Some uu____8774 in
                                   solve_prob orig uu____8772
                                     [TERM (u, proj)] wl1 in
                                 let uu____8779 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_55  -> Some _0_55) uu____8779))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8803 = lhs in
          match uu____8803 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8826 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____8826 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8848 =
                        let uu____8874 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____8874) in
                      Some uu____8848
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____8957 =
                           let uu____8961 =
                             let uu____8962 = FStar_Syntax_Subst.compress k in
                             uu____8962.FStar_Syntax_Syntax.n in
                           (uu____8961, args) in
                         match uu____8957 with
                         | (uu____8969,[]) ->
                             let uu____8971 =
                               let uu____8977 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____8977) in
                             Some uu____8971
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____8988,uu____8989) ->
                             let uu____9000 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9000 with
                              | (uv1,uv_args) ->
                                  let uu____9029 =
                                    let uu____9030 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9030.FStar_Syntax_Syntax.n in
                                  (match uu____9029 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9037) ->
                                       let uu____9050 =
                                         pat_vars env [] uv_args in
                                       (match uu____9050 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9064  ->
                                                      let uu____9065 =
                                                        let uu____9066 =
                                                          let uu____9067 =
                                                            let uu____9070 =
                                                              let uu____9071
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9071
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9070 in
                                                          fst uu____9067 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9066 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9065)) in
                                            let c1 =
                                              let uu____9077 =
                                                let uu____9078 =
                                                  let uu____9081 =
                                                    let uu____9082 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9082
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9081 in
                                                fst uu____9078 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9077 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9091 =
                                                let uu____9098 =
                                                  let uu____9104 =
                                                    let uu____9105 =
                                                      let uu____9108 =
                                                        let uu____9109 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9109
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9108 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9105 in
                                                  FStar_Util.Inl uu____9104 in
                                                Some uu____9098 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9091 in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             Some (xs1, c1)))
                                   | uu____9132 -> None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9135,uu____9136)
                             ->
                             let uu____9148 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9148 with
                              | (uv1,uv_args) ->
                                  let uu____9177 =
                                    let uu____9178 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9178.FStar_Syntax_Syntax.n in
                                  (match uu____9177 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9185) ->
                                       let uu____9198 =
                                         pat_vars env [] uv_args in
                                       (match uu____9198 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9212  ->
                                                      let uu____9213 =
                                                        let uu____9214 =
                                                          let uu____9215 =
                                                            let uu____9218 =
                                                              let uu____9219
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9219
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9218 in
                                                          fst uu____9215 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9214 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9213)) in
                                            let c1 =
                                              let uu____9225 =
                                                let uu____9226 =
                                                  let uu____9229 =
                                                    let uu____9230 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9230
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9229 in
                                                fst uu____9226 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9225 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9239 =
                                                let uu____9246 =
                                                  let uu____9252 =
                                                    let uu____9253 =
                                                      let uu____9256 =
                                                        let uu____9257 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9257
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9256 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9253 in
                                                  FStar_Util.Inl uu____9252 in
                                                Some uu____9246 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9239 in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             Some (xs1, c1)))
                                   | uu____9280 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9285)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____9311 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____9311
                                 (fun _0_56  -> Some _0_56)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9330 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____9330 with
                                  | (args1,rest) ->
                                      let uu____9346 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____9346 with
                                       | (xs2,c2) ->
                                           let uu____9354 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____9354
                                             (fun uu____9365  ->
                                                match uu____9365 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9387 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____9387 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____9433 =
                                        let uu____9436 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9436 in
                                      FStar_All.pipe_right uu____9433
                                        (fun _0_57  -> Some _0_57))
                         | uu____9444 ->
                             let uu____9448 =
                               let uu____9449 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____9453 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____9454 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9449 uu____9453 uu____9454 in
                             failwith uu____9448 in
                       let uu____9458 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____9458
                         (fun uu____9486  ->
                            match uu____9486 with
                            | (xs1,c1) ->
                                let uu____9514 =
                                  let uu____9537 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9537) in
                                Some uu____9514)) in
              let rec imitate_or_project n1 stopt i =
                if (i >= n1) || (FStar_Option.isNone stopt)
                then
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig
                else
                  (let st = FStar_Option.get stopt in
                   let tx = FStar_Unionfind.new_transaction () in
                   if i = (- (Prims.parse_int "1"))
                   then
                     let uu____9609 = imitate orig env wl1 st in
                     match uu____9609 with
                     | Failed uu____9614 ->
                         (FStar_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9620 = project orig env wl1 i st in
                      match uu____9620 with
                      | None  ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some (Failed uu____9627) ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____9641 = FStar_Syntax_Util.head_and_args t21 in
                match uu____9641 with
                | (hd1,uu____9652) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9667 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9675 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9676 -> true
                     | uu____9691 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____9694 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____9694
                         then true
                         else
                           ((let uu____9697 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____9697
                             then
                               let uu____9698 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9698
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9706 =
                    let uu____9709 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____9709 FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____9706 FStar_Syntax_Free.names in
                let uu____9740 = FStar_Util.set_is_empty fvs_hd in
                if uu____9740
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____9749 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____9749 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9757 =
                            let uu____9758 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____9758 in
                          giveup_or_defer1 orig uu____9757
                        else
                          (let uu____9760 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____9760
                           then
                             let uu____9761 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____9761
                              then
                                let uu____9762 = subterms args_lhs in
                                imitate' orig env wl1 uu____9762
                              else
                                ((let uu____9766 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____9766
                                  then
                                    let uu____9767 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____9768 = names_to_string fvs1 in
                                    let uu____9769 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9767 uu____9768 uu____9769
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9774 ->
                                        let uu____9775 = sn_binders env vars in
                                        u_abs k_uv uu____9775 t21 in
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
                               (let uu____9784 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____9784
                                then
                                  ((let uu____9786 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____9786
                                    then
                                      let uu____9787 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____9788 = names_to_string fvs1 in
                                      let uu____9789 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9787 uu____9788 uu____9789
                                    else ());
                                   (let uu____9791 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9791
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
                     (let uu____9802 =
                        let uu____9803 = FStar_Syntax_Free.names t1 in
                        check_head uu____9803 t2 in
                      if uu____9802
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____9807 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____9807
                          then
                            let uu____9808 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9808
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9811 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9811 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9853 =
               match uu____9853 with
               | (t,u,k,args) ->
                   let uu____9883 = FStar_Syntax_Util.arrow_formals k in
                   (match uu____9883 with
                    | (all_formals,uu____9894) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____9986  ->
                                        match uu____9986 with
                                        | (x,imp) ->
                                            let uu____9993 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____9993, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____10001 = FStar_Syntax_Util.type_u () in
                                match uu____10001 with
                                | (t1,uu____10005) ->
                                    let uu____10006 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    fst uu____10006 in
                              let uu____10009 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____10009 with
                               | (t',tm_u1) ->
                                   let uu____10016 = destruct_flex_t t' in
                                   (match uu____10016 with
                                    | (uu____10036,u1,k1,uu____10039) ->
                                        let sol =
                                          let uu____10067 =
                                            let uu____10072 =
                                              u_abs k all_formals t' in
                                            ((u, k), uu____10072) in
                                          TERM uu____10067 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k1, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10132 = pat_var_opt env pat_args hd1 in
                              (match uu____10132 with
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
                                              (fun uu____10161  ->
                                                 match uu____10161 with
                                                 | (x,uu____10165) ->
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
                                      let uu____10171 =
                                        let uu____10172 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____10172 in
                                      if uu____10171
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10176 =
                                           FStar_Util.set_add (fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10176 formals1
                                           tl1)))
                          | uu____10182 -> failwith "Impossible" in
                        let uu____10193 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____10193 all_formals args) in
             let solve_both_pats wl1 uu____10241 uu____10242 r =
               match (uu____10241, uu____10242) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10396 =
                     (FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys) in
                   if uu____10396
                   then
                     let uu____10400 = solve_prob orig None [] wl1 in
                     solve env uu____10400
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____10415 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____10415
                       then
                         let uu____10416 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____10417 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____10418 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____10419 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____10420 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10416 uu____10417 uu____10418 uu____10419
                           uu____10420
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____10462 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____10462 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10470 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____10470 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10500 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10500 in
                                  let uu____10503 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____10503 k3)
                           else
                             (let uu____10506 =
                                let uu____10507 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____10508 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____10509 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10507 uu____10508 uu____10509 in
                              failwith uu____10506) in
                       let uu____10510 =
                         let uu____10516 =
                           let uu____10524 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____10524 in
                         match uu____10516 with
                         | (bs,k1') ->
                             let uu____10542 =
                               let uu____10550 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____10550 in
                             (match uu____10542 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____10571 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_58  ->
                                         FStar_TypeChecker_Common.TProb _0_58)
                                      uu____10571 in
                                  let uu____10576 =
                                    let uu____10579 =
                                      let uu____10580 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____10580.FStar_Syntax_Syntax.n in
                                    let uu____10583 =
                                      let uu____10584 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____10584.FStar_Syntax_Syntax.n in
                                    (uu____10579, uu____10583) in
                                  (match uu____10576 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10592,uu____10593) ->
                                       (k1', [sub_prob])
                                   | (uu____10597,FStar_Syntax_Syntax.Tm_type
                                      uu____10598) -> (k2', [sub_prob])
                                   | uu____10602 ->
                                       let uu____10605 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____10605 with
                                        | (t,uu____10614) ->
                                            let uu____10615 = new_uvar r zs t in
                                            (match uu____10615 with
                                             | (k_zs,uu____10624) ->
                                                 let kprob =
                                                   let uu____10626 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_59  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_59) uu____10626 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____10510 with
                       | (k_u',sub_probs) ->
                           let uu____10640 =
                             let uu____10648 =
                               let uu____10649 = new_uvar r zs k_u' in
                               FStar_All.pipe_left FStar_Pervasives.fst
                                 uu____10649 in
                             let uu____10654 =
                               let uu____10657 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____10657 in
                             let uu____10660 =
                               let uu____10663 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____10663 in
                             (uu____10648, uu____10654, uu____10660) in
                           (match uu____10640 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____10682 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____10682 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____10706 =
                                          FStar_Unionfind.equivalent u1 u2 in
                                        if uu____10706
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____10713 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____10713 with
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
             let solve_one_pat uu____10765 uu____10766 =
               match (uu____10765, uu____10766) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10870 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____10870
                     then
                       let uu____10871 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10872 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10871 uu____10872
                     else ());
                    (let uu____10874 = FStar_Unionfind.equivalent u1 u2 in
                     if uu____10874
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10884  ->
                              fun uu____10885  ->
                                match (uu____10884, uu____10885) with
                                | ((a,uu____10895),(t21,uu____10897)) ->
                                    let uu____10902 =
                                      let uu____10905 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____10905
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____10902
                                      (fun _0_60  ->
                                         FStar_TypeChecker_Common.TProb _0_60))
                           xs args2 in
                       let guard =
                         let uu____10909 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____10909 in
                       let wl1 = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____10919 = occurs_check env wl (u1, k1) t21 in
                        match uu____10919 with
                        | (occurs_ok,uu____10928) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____10933 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____10933
                            then
                              let sol =
                                let uu____10935 =
                                  let uu____10940 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____10940) in
                                TERM uu____10935 in
                              let wl1 = solve_prob orig None [sol] wl in
                              solve env wl1
                            else
                              (let uu____10953 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____10953
                               then
                                 let uu____10954 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____10954 with
                                 | (sol,(uu____10968,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____10978 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____10978
                                       then
                                         let uu____10979 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10979
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10984 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____10986 = lhs in
             match uu____10986 with
             | (t1,u1,k1,args1) ->
                 let uu____10991 = rhs in
                 (match uu____10991 with
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
                       | uu____11017 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____11023 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____11023 with
                              | (sol,uu____11030) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____11033 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____11033
                                    then
                                      let uu____11034 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____11034
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____11039 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____11041 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____11041
        then
          let uu____11042 = solve_prob orig None [] wl in
          solve env uu____11042
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____11046 = FStar_Util.physical_equality t1 t2 in
           if uu____11046
           then
             let uu____11047 = solve_prob orig None [] wl in
             solve env uu____11047
           else
             ((let uu____11050 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____11050
               then
                 let uu____11051 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____11051
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____11054,uu____11055) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____11056,FStar_Syntax_Syntax.Tm_bvar uu____11057) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___130_11097 =
                     match uu___130_11097 with
                     | [] -> c
                     | bs ->
                         let uu____11111 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c)) None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____11111 in
                   let uu____11121 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____11121 with
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
                                   let uu____11207 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____11207
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____11209 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.CProb _0_61)
                                   uu____11209))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___131_11286 =
                     match uu___131_11286 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l)) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____11321 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____11321 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11404 =
                                   let uu____11407 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____11408 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____11407
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11408 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_TypeChecker_Common.TProb _0_62)
                                   uu____11404))
               | (FStar_Syntax_Syntax.Tm_abs uu____11411,uu____11412) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11435 -> true
                     | uu____11450 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11478 =
                     let uu____11489 = maybe_eta t1 in
                     let uu____11494 = maybe_eta t2 in
                     (uu____11489, uu____11494) in
                   (match uu____11478 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___164_11525 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___164_11525.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___164_11525.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___164_11525.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___164_11525.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___164_11525.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___164_11525.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___164_11525.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___164_11525.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11544 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11544
                        then
                          let uu____11545 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11545 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11566 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11566
                        then
                          let uu____11567 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11567 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11572 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11583,FStar_Syntax_Syntax.Tm_abs uu____11584) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11607 -> true
                     | uu____11622 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11650 =
                     let uu____11661 = maybe_eta t1 in
                     let uu____11666 = maybe_eta t2 in
                     (uu____11661, uu____11666) in
                   (match uu____11650 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___164_11697 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___164_11697.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___164_11697.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___164_11697.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___164_11697.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___164_11697.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___164_11697.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___164_11697.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___164_11697.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11716 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11716
                        then
                          let uu____11717 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11717 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11738 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11738
                        then
                          let uu____11739 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11739 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11744 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11755,FStar_Syntax_Syntax.Tm_refine uu____11756) ->
                   let uu____11765 = as_refinement env wl t1 in
                   (match uu____11765 with
                    | (x1,phi1) ->
                        let uu____11770 = as_refinement env wl t2 in
                        (match uu____11770 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11776 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_63  ->
                                    FStar_TypeChecker_Common.TProb _0_63)
                                 uu____11776 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____11809 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____11809
                                 (guard_on_element wl problem x11) in
                             let fallback uu____11813 =
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
                                 let uu____11819 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____11819 impl in
                               let wl1 = solve_prob orig (Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11826 =
                                   let uu____11829 =
                                     let uu____11830 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____11830 :: (p_scope orig) in
                                   mk_problem uu____11829 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____11826 in
                               let uu____11833 =
                                 solve env1
                                   (let uu___165_11834 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___165_11834.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___165_11834.smt_ok);
                                      tcenv = (uu___165_11834.tcenv)
                                    }) in
                               (match uu____11833 with
                                | Failed uu____11838 -> fallback ()
                                | Success uu____11841 ->
                                    let guard =
                                      let uu____11845 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives.fst in
                                      let uu____11848 =
                                        let uu____11849 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives.fst in
                                        FStar_All.pipe_right uu____11849
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____11845
                                        uu____11848 in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl2 =
                                      let uu___166_11856 = wl1 in
                                      {
                                        attempting =
                                          (uu___166_11856.attempting);
                                        wl_deferred =
                                          (uu___166_11856.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___166_11856.defer_ok);
                                        smt_ok = (uu___166_11856.smt_ok);
                                        tcenv = (uu___166_11856.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11858,FStar_Syntax_Syntax.Tm_uvar uu____11859) ->
                   let uu____11876 = destruct_flex_t t1 in
                   let uu____11877 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11876 uu____11877
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11878;
                     FStar_Syntax_Syntax.tk = uu____11879;
                     FStar_Syntax_Syntax.pos = uu____11880;
                     FStar_Syntax_Syntax.vars = uu____11881;_},uu____11882),FStar_Syntax_Syntax.Tm_uvar
                  uu____11883) ->
                   let uu____11914 = destruct_flex_t t1 in
                   let uu____11915 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11914 uu____11915
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11916,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11917;
                     FStar_Syntax_Syntax.tk = uu____11918;
                     FStar_Syntax_Syntax.pos = uu____11919;
                     FStar_Syntax_Syntax.vars = uu____11920;_},uu____11921))
                   ->
                   let uu____11952 = destruct_flex_t t1 in
                   let uu____11953 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11952 uu____11953
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11954;
                     FStar_Syntax_Syntax.tk = uu____11955;
                     FStar_Syntax_Syntax.pos = uu____11956;
                     FStar_Syntax_Syntax.vars = uu____11957;_},uu____11958),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11959;
                     FStar_Syntax_Syntax.tk = uu____11960;
                     FStar_Syntax_Syntax.pos = uu____11961;
                     FStar_Syntax_Syntax.vars = uu____11962;_},uu____11963))
                   ->
                   let uu____12008 = destruct_flex_t t1 in
                   let uu____12009 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12008 uu____12009
               | (FStar_Syntax_Syntax.Tm_uvar uu____12010,uu____12011) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12020 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____12020 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12024;
                     FStar_Syntax_Syntax.tk = uu____12025;
                     FStar_Syntax_Syntax.pos = uu____12026;
                     FStar_Syntax_Syntax.vars = uu____12027;_},uu____12028),uu____12029)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12052 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____12052 t2 wl
               | (uu____12056,FStar_Syntax_Syntax.Tm_uvar uu____12057) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____12066,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12067;
                     FStar_Syntax_Syntax.tk = uu____12068;
                     FStar_Syntax_Syntax.pos = uu____12069;
                     FStar_Syntax_Syntax.vars = uu____12070;_},uu____12071))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12094,FStar_Syntax_Syntax.Tm_type uu____12095) ->
                   solve_t' env
                     (let uu___167_12104 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12104.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12104.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12104.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12104.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12104.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12104.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12104.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12104.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12104.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12105;
                     FStar_Syntax_Syntax.tk = uu____12106;
                     FStar_Syntax_Syntax.pos = uu____12107;
                     FStar_Syntax_Syntax.vars = uu____12108;_},uu____12109),FStar_Syntax_Syntax.Tm_type
                  uu____12110) ->
                   solve_t' env
                     (let uu___167_12133 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12133.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12133.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12133.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12133.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12133.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12133.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12133.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12133.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12133.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12134,FStar_Syntax_Syntax.Tm_arrow uu____12135) ->
                   solve_t' env
                     (let uu___167_12151 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12151.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12151.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12151.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12151.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12151.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12151.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12151.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12151.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12151.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12152;
                     FStar_Syntax_Syntax.tk = uu____12153;
                     FStar_Syntax_Syntax.pos = uu____12154;
                     FStar_Syntax_Syntax.vars = uu____12155;_},uu____12156),FStar_Syntax_Syntax.Tm_arrow
                  uu____12157) ->
                   solve_t' env
                     (let uu___167_12187 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12187.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12187.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12187.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12187.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12187.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12187.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12187.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12187.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12187.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____12188,uu____12189) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12200 =
                        let uu____12201 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12201 in
                      if uu____12200
                      then
                        let uu____12202 =
                          FStar_All.pipe_left
                            (fun _0_65  ->
                               FStar_TypeChecker_Common.TProb _0_65)
                            (let uu___168_12205 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_12205.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_12205.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_12205.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_12205.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_12205.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___168_12205.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_12205.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_12205.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_12205.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12206 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12202 uu____12206 t2
                          wl
                      else
                        (let uu____12211 = base_and_refinement env wl t2 in
                         match uu____12211 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12241 =
                                    FStar_All.pipe_left
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66)
                                      (let uu___169_12244 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___169_12244.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___169_12244.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___169_12244.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___169_12244.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___169_12244.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___169_12244.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___169_12244.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___169_12244.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___169_12244.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12245 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12241
                                    uu____12245 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___170_12260 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___170_12260.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___170_12260.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12263 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67)
                                      uu____12263 in
                                  let guard =
                                    let uu____12271 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12271
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12277;
                     FStar_Syntax_Syntax.tk = uu____12278;
                     FStar_Syntax_Syntax.pos = uu____12279;
                     FStar_Syntax_Syntax.vars = uu____12280;_},uu____12281),uu____12282)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12307 =
                        let uu____12308 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12308 in
                      if uu____12307
                      then
                        let uu____12309 =
                          FStar_All.pipe_left
                            (fun _0_68  ->
                               FStar_TypeChecker_Common.TProb _0_68)
                            (let uu___168_12312 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_12312.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_12312.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_12312.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_12312.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_12312.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___168_12312.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_12312.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_12312.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_12312.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12313 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12309 uu____12313 t2
                          wl
                      else
                        (let uu____12318 = base_and_refinement env wl t2 in
                         match uu____12318 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12348 =
                                    FStar_All.pipe_left
                                      (fun _0_69  ->
                                         FStar_TypeChecker_Common.TProb _0_69)
                                      (let uu___169_12351 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___169_12351.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___169_12351.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___169_12351.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___169_12351.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___169_12351.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___169_12351.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___169_12351.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___169_12351.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___169_12351.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12352 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12348
                                    uu____12352 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___170_12367 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___170_12367.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___170_12367.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12370 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_70  ->
                                         FStar_TypeChecker_Common.TProb _0_70)
                                      uu____12370 in
                                  let guard =
                                    let uu____12378 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12378
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12384,FStar_Syntax_Syntax.Tm_uvar uu____12385) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12395 = base_and_refinement env wl t1 in
                      match uu____12395 with
                      | (t_base,uu____12406) ->
                          solve_t env
                            (let uu___171_12421 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_12421.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_12421.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_12421.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_12421.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___171_12421.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_12421.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_12421.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_12421.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12424,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12425;
                     FStar_Syntax_Syntax.tk = uu____12426;
                     FStar_Syntax_Syntax.pos = uu____12427;
                     FStar_Syntax_Syntax.vars = uu____12428;_},uu____12429))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12453 = base_and_refinement env wl t1 in
                      match uu____12453 with
                      | (t_base,uu____12464) ->
                          solve_t env
                            (let uu___171_12479 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_12479.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_12479.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_12479.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_12479.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___171_12479.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_12479.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_12479.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_12479.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12482,uu____12483) ->
                   let t21 =
                     let uu____12491 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____12491 in
                   solve_t env
                     (let uu___172_12504 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___172_12504.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___172_12504.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___172_12504.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___172_12504.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___172_12504.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___172_12504.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___172_12504.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___172_12504.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___172_12504.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12505,FStar_Syntax_Syntax.Tm_refine uu____12506) ->
                   let t11 =
                     let uu____12514 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____12514 in
                   solve_t env
                     (let uu___173_12527 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_12527.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___173_12527.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___173_12527.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___173_12527.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_12527.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_12527.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_12527.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_12527.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_12527.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12530,uu____12531) ->
                   let head1 =
                     let uu____12550 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12550 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12581 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12581 FStar_Pervasives.fst in
                   let uu____12609 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12609
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12618 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12618
                      then
                        let guard =
                          let uu____12625 =
                            let uu____12626 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12626 = FStar_Syntax_Util.Equal in
                          if uu____12625
                          then None
                          else
                            (let uu____12629 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_71  -> Some _0_71)
                               uu____12629) in
                        let uu____12631 = solve_prob orig guard [] wl in
                        solve env uu____12631
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12634,uu____12635) ->
                   let head1 =
                     let uu____12643 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12643 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12674 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12674 FStar_Pervasives.fst in
                   let uu____12702 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12702
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12711 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12711
                      then
                        let guard =
                          let uu____12718 =
                            let uu____12719 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12719 = FStar_Syntax_Util.Equal in
                          if uu____12718
                          then None
                          else
                            (let uu____12722 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_72  -> Some _0_72)
                               uu____12722) in
                        let uu____12724 = solve_prob orig guard [] wl in
                        solve env uu____12724
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12727,uu____12728) ->
                   let head1 =
                     let uu____12732 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12732 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12763 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12763 FStar_Pervasives.fst in
                   let uu____12791 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12791
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12800 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12800
                      then
                        let guard =
                          let uu____12807 =
                            let uu____12808 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12808 = FStar_Syntax_Util.Equal in
                          if uu____12807
                          then None
                          else
                            (let uu____12811 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_73  -> Some _0_73)
                               uu____12811) in
                        let uu____12813 = solve_prob orig guard [] wl in
                        solve env uu____12813
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12816,uu____12817) ->
                   let head1 =
                     let uu____12821 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12821 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12852 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12852 FStar_Pervasives.fst in
                   let uu____12880 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12880
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12889 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12889
                      then
                        let guard =
                          let uu____12896 =
                            let uu____12897 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12897 = FStar_Syntax_Util.Equal in
                          if uu____12896
                          then None
                          else
                            (let uu____12900 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_74  -> Some _0_74)
                               uu____12900) in
                        let uu____12902 = solve_prob orig guard [] wl in
                        solve env uu____12902
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____12905,uu____12906) ->
                   let head1 =
                     let uu____12910 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12910 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12941 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12941 FStar_Pervasives.fst in
                   let uu____12969 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12969
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12978 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12978
                      then
                        let guard =
                          let uu____12985 =
                            let uu____12986 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12986 = FStar_Syntax_Util.Equal in
                          if uu____12985
                          then None
                          else
                            (let uu____12989 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_75  -> Some _0_75)
                               uu____12989) in
                        let uu____12991 = solve_prob orig guard [] wl in
                        solve env uu____12991
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____12994,uu____12995) ->
                   let head1 =
                     let uu____13008 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13008 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13039 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13039 FStar_Pervasives.fst in
                   let uu____13067 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13067
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13076 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13076
                      then
                        let guard =
                          let uu____13083 =
                            let uu____13084 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13084 = FStar_Syntax_Util.Equal in
                          if uu____13083
                          then None
                          else
                            (let uu____13087 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_76  -> Some _0_76)
                               uu____13087) in
                        let uu____13089 = solve_prob orig guard [] wl in
                        solve env uu____13089
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13092,FStar_Syntax_Syntax.Tm_match uu____13093) ->
                   let head1 =
                     let uu____13112 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13112 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13143 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13143 FStar_Pervasives.fst in
                   let uu____13171 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13171
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13180 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13180
                      then
                        let guard =
                          let uu____13187 =
                            let uu____13188 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13188 = FStar_Syntax_Util.Equal in
                          if uu____13187
                          then None
                          else
                            (let uu____13191 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_77  -> Some _0_77)
                               uu____13191) in
                        let uu____13193 = solve_prob orig guard [] wl in
                        solve env uu____13193
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13196,FStar_Syntax_Syntax.Tm_uinst uu____13197) ->
                   let head1 =
                     let uu____13205 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13205 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13236 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13236 FStar_Pervasives.fst in
                   let uu____13264 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13264
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13273 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13273
                      then
                        let guard =
                          let uu____13280 =
                            let uu____13281 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13281 = FStar_Syntax_Util.Equal in
                          if uu____13280
                          then None
                          else
                            (let uu____13284 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_78  -> Some _0_78)
                               uu____13284) in
                        let uu____13286 = solve_prob orig guard [] wl in
                        solve env uu____13286
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13289,FStar_Syntax_Syntax.Tm_name uu____13290) ->
                   let head1 =
                     let uu____13294 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13294 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13325 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13325 FStar_Pervasives.fst in
                   let uu____13353 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13353
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13362 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13362
                      then
                        let guard =
                          let uu____13369 =
                            let uu____13370 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13370 = FStar_Syntax_Util.Equal in
                          if uu____13369
                          then None
                          else
                            (let uu____13373 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_79  -> Some _0_79)
                               uu____13373) in
                        let uu____13375 = solve_prob orig guard [] wl in
                        solve env uu____13375
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13378,FStar_Syntax_Syntax.Tm_constant uu____13379) ->
                   let head1 =
                     let uu____13383 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13383 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13414 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13414 FStar_Pervasives.fst in
                   let uu____13442 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13442
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13451 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13451
                      then
                        let guard =
                          let uu____13458 =
                            let uu____13459 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13459 = FStar_Syntax_Util.Equal in
                          if uu____13458
                          then None
                          else
                            (let uu____13462 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_80  -> Some _0_80)
                               uu____13462) in
                        let uu____13464 = solve_prob orig guard [] wl in
                        solve env uu____13464
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13467,FStar_Syntax_Syntax.Tm_fvar uu____13468) ->
                   let head1 =
                     let uu____13472 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13472 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13503 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13503 FStar_Pervasives.fst in
                   let uu____13531 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13531
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13540 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13540
                      then
                        let guard =
                          let uu____13547 =
                            let uu____13548 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13548 = FStar_Syntax_Util.Equal in
                          if uu____13547
                          then None
                          else
                            (let uu____13551 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_81  -> Some _0_81)
                               uu____13551) in
                        let uu____13553 = solve_prob orig guard [] wl in
                        solve env uu____13553
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13556,FStar_Syntax_Syntax.Tm_app uu____13557) ->
                   let head1 =
                     let uu____13570 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13570 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13601 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13601 FStar_Pervasives.fst in
                   let uu____13629 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13629
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13638 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13638
                      then
                        let guard =
                          let uu____13645 =
                            let uu____13646 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13646 = FStar_Syntax_Util.Equal in
                          if uu____13645
                          then None
                          else
                            (let uu____13649 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_82  -> Some _0_82)
                               uu____13649) in
                        let uu____13651 = solve_prob orig guard [] wl in
                        solve env uu____13651
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13655,uu____13656),uu____13657) ->
                   solve_t' env
                     (let uu___174_13686 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_13686.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___174_13686.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___174_13686.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___174_13686.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_13686.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_13686.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_13686.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_13686.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_13686.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13689,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13691,uu____13692)) ->
                   solve_t' env
                     (let uu___175_13721 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_13721.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___175_13721.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___175_13721.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___175_13721.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_13721.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_13721.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_13721.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_13721.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_13721.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13722,uu____13723) ->
                   let uu____13731 =
                     let uu____13732 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13733 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13732
                       uu____13733 in
                   failwith uu____13731
               | (FStar_Syntax_Syntax.Tm_meta uu____13734,uu____13735) ->
                   let uu____13740 =
                     let uu____13741 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13742 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13741
                       uu____13742 in
                   failwith uu____13740
               | (FStar_Syntax_Syntax.Tm_delayed uu____13743,uu____13744) ->
                   let uu____13765 =
                     let uu____13766 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13767 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13766
                       uu____13767 in
                   failwith uu____13765
               | (uu____13768,FStar_Syntax_Syntax.Tm_meta uu____13769) ->
                   let uu____13774 =
                     let uu____13775 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13776 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13775
                       uu____13776 in
                   failwith uu____13774
               | (uu____13777,FStar_Syntax_Syntax.Tm_delayed uu____13778) ->
                   let uu____13799 =
                     let uu____13800 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13801 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13800
                       uu____13801 in
                   failwith uu____13799
               | (uu____13802,FStar_Syntax_Syntax.Tm_let uu____13803) ->
                   let uu____13811 =
                     let uu____13812 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13813 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13812
                       uu____13813 in
                   failwith uu____13811
               | uu____13814 -> giveup env "head tag mismatch" orig)))
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
          (let uu____13846 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____13846
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____13854  ->
                  fun uu____13855  ->
                    match (uu____13854, uu____13855) with
                    | ((a1,uu____13865),(a2,uu____13867)) ->
                        let uu____13872 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_83  -> FStar_TypeChecker_Common.TProb _0_83)
                          uu____13872)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____13878 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p) FStar_Pervasives.fst)
                 sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____13878 in
           let wl1 = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____13898 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____13905)::[] -> wp1
              | uu____13918 ->
                  let uu____13924 =
                    let uu____13925 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____13925 in
                  failwith uu____13924 in
            let uu____13928 =
              let uu____13934 =
                let uu____13935 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____13935 in
              [uu____13934] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____13928;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____13936 = lift_c1 () in solve_eq uu____13936 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___132_13940  ->
                       match uu___132_13940 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____13941 -> false)) in
             let uu____13942 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____13966)::uu____13967,(wp2,uu____13969)::uu____13970)
                   -> (wp1, wp2)
               | uu____14011 ->
                   let uu____14024 =
                     let uu____14025 =
                       let uu____14028 =
                         let uu____14029 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____14030 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____14029 uu____14030 in
                       (uu____14028, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____14025 in
                   raise uu____14024 in
             match uu____13942 with
             | (wpc1,wpc2) ->
                 let uu____14047 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____14047
                 then
                   let uu____14050 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env uu____14050 wl
                 else
                   (let uu____14054 =
                      let uu____14058 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____14058 in
                    match uu____14054 with
                    | (c2_decl,qualifiers) ->
                        let uu____14070 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____14070
                        then
                          let c1_repr =
                            let uu____14073 =
                              let uu____14074 =
                                let uu____14075 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____14075 in
                              let uu____14076 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14074 uu____14076 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14073 in
                          let c2_repr =
                            let uu____14078 =
                              let uu____14079 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____14080 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14079 uu____14080 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14078 in
                          let prob =
                            let uu____14082 =
                              let uu____14085 =
                                let uu____14086 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____14087 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____14086
                                  uu____14087 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____14085 in
                            FStar_TypeChecker_Common.TProb uu____14082 in
                          let wl1 =
                            let uu____14089 =
                              let uu____14091 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives.fst in
                              Some uu____14091 in
                            solve_prob orig uu____14089 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____14098 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____14098
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____14100 =
                                     let uu____14103 =
                                       let uu____14104 =
                                         let uu____14114 =
                                           let uu____14115 =
                                             let uu____14116 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____14116] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____14115 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____14117 =
                                           let uu____14119 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____14120 =
                                             let uu____14122 =
                                               let uu____14123 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____14123 in
                                             [uu____14122] in
                                           uu____14119 :: uu____14120 in
                                         (uu____14114, uu____14117) in
                                       FStar_Syntax_Syntax.Tm_app uu____14104 in
                                     FStar_Syntax_Syntax.mk uu____14103 in
                                   uu____14100
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____14134 =
                                    let uu____14137 =
                                      let uu____14138 =
                                        let uu____14148 =
                                          let uu____14149 =
                                            let uu____14150 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____14150] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____14149 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____14151 =
                                          let uu____14153 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____14154 =
                                            let uu____14156 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____14157 =
                                              let uu____14159 =
                                                let uu____14160 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14160 in
                                              [uu____14159] in
                                            uu____14156 :: uu____14157 in
                                          uu____14153 :: uu____14154 in
                                        (uu____14148, uu____14151) in
                                      FStar_Syntax_Syntax.Tm_app uu____14138 in
                                    FStar_Syntax_Syntax.mk uu____14137 in
                                  uu____14134
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____14171 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_TypeChecker_Common.TProb _0_84)
                               uu____14171 in
                           let wl1 =
                             let uu____14177 =
                               let uu____14179 =
                                 let uu____14182 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____14182 g in
                               FStar_All.pipe_left (fun _0_85  -> Some _0_85)
                                 uu____14179 in
                             solve_prob orig uu____14177 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____14192 = FStar_Util.physical_equality c1 c2 in
        if uu____14192
        then
          let uu____14193 = solve_prob orig None [] wl in
          solve env uu____14193
        else
          ((let uu____14196 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____14196
            then
              let uu____14197 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____14198 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14197
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14198
            else ());
           (let uu____14200 =
              let uu____14203 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____14204 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____14203, uu____14204) in
            match uu____14200 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14208),FStar_Syntax_Syntax.Total
                    (t2,uu____14210)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14223 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14223 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14226,FStar_Syntax_Syntax.Total uu____14227) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14239),FStar_Syntax_Syntax.Total
                    (t2,uu____14241)) ->
                     let uu____14254 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14254 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14258),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14260)) ->
                     let uu____14273 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14273 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14277),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14279)) ->
                     let uu____14292 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14292 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14295,FStar_Syntax_Syntax.Comp uu____14296) ->
                     let uu____14302 =
                       let uu___176_14305 = problem in
                       let uu____14308 =
                         let uu____14309 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14309 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_14305.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14308;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_14305.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_14305.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_14305.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_14305.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_14305.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_14305.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_14305.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_14305.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14302 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14310,FStar_Syntax_Syntax.Comp uu____14311) ->
                     let uu____14317 =
                       let uu___176_14320 = problem in
                       let uu____14323 =
                         let uu____14324 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14324 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_14320.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14323;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_14320.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_14320.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_14320.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_14320.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_14320.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_14320.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_14320.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_14320.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14317 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14325,FStar_Syntax_Syntax.GTotal uu____14326) ->
                     let uu____14332 =
                       let uu___177_14335 = problem in
                       let uu____14338 =
                         let uu____14339 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14339 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14335.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_14335.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14335.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14338;
                         FStar_TypeChecker_Common.element =
                           (uu___177_14335.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14335.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14335.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14335.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14335.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14335.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14332 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14340,FStar_Syntax_Syntax.Total uu____14341) ->
                     let uu____14347 =
                       let uu___177_14350 = problem in
                       let uu____14353 =
                         let uu____14354 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14354 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14350.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_14350.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14350.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14353;
                         FStar_TypeChecker_Common.element =
                           (uu___177_14350.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14350.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14350.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14350.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14350.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14350.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14347 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14355,FStar_Syntax_Syntax.Comp uu____14356) ->
                     let uu____14357 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____14357
                     then
                       let uu____14358 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type" in
                       solve_t env uu____14358 wl
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
                           (let uu____14368 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____14368
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14370 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____14370 with
                            | None  ->
                                let uu____14372 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14373 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____14373) in
                                if uu____14372
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
                                  (let uu____14376 =
                                     let uu____14377 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____14378 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14377 uu____14378 in
                                   giveup env uu____14376 orig)
                            | Some edge -> solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14383 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14403  ->
              match uu____14403 with
              | (uu____14414,uu____14415,u,uu____14417,uu____14418,uu____14419)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____14383 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14448 =
        FStar_All.pipe_right (fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____14448 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____14458 =
        FStar_All.pipe_right (snd ineqs)
          (FStar_List.map
             (fun uu____14470  ->
                match uu____14470 with
                | (u1,u2) ->
                    let uu____14475 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____14476 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____14475 uu____14476)) in
      FStar_All.pipe_right uu____14458 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14488,[])) -> "{}"
      | uu____14501 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14511 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____14511
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____14514 =
              FStar_List.map
                (fun uu____14518  ->
                   match uu____14518 with
                   | (uu____14521,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____14514 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____14525 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14525 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14563 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____14563
    then
      let uu____14564 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____14565 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14564
        (rel_to_string rel) uu____14565
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
            let uu____14585 =
              let uu____14587 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_86  -> Some _0_86) uu____14587 in
            FStar_Syntax_Syntax.new_bv uu____14585 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____14593 =
              let uu____14595 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_87  -> Some _0_87) uu____14595 in
            let uu____14597 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____14593 uu____14597 in
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
          let uu____14620 = FStar_Options.eager_inference () in
          if uu____14620
          then
            let uu___178_14621 = probs in
            {
              attempting = (uu___178_14621.attempting);
              wl_deferred = (uu___178_14621.wl_deferred);
              ctr = (uu___178_14621.ctr);
              defer_ok = false;
              smt_ok = (uu___178_14621.smt_ok);
              tcenv = (uu___178_14621.tcenv)
            }
          else probs in
        let tx = FStar_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred -> (FStar_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Unionfind.rollback tx;
             (let uu____14632 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____14632
              then
                let uu____14633 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____14633
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
          ((let uu____14643 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____14643
            then
              let uu____14644 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14644
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____14648 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____14648
             then
               let uu____14649 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14649
             else ());
            (let f2 =
               let uu____14652 =
                 let uu____14653 = FStar_Syntax_Util.unmeta f1 in
                 uu____14653.FStar_Syntax_Syntax.n in
               match uu____14652 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14657 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___179_14658 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___179_14658.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___179_14658.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___179_14658.FStar_TypeChecker_Env.implicits)
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
            let uu____14673 =
              let uu____14674 =
                let uu____14675 =
                  let uu____14676 =
                    FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____14676
                    (fun _0_88  -> FStar_TypeChecker_Common.NonTrivial _0_88) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14675;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____14674 in
            FStar_All.pipe_left (fun _0_89  -> Some _0_89) uu____14673
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____14709 =
        let uu____14710 =
          let uu____14711 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
          FStar_All.pipe_right uu____14711
            (fun _0_90  -> FStar_TypeChecker_Common.NonTrivial _0_90) in
        {
          FStar_TypeChecker_Env.guard_f = uu____14710;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      Some uu____14709
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
          (let uu____14737 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14737
           then
             let uu____14738 = FStar_Syntax_Print.term_to_string t1 in
             let uu____14739 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14738
               uu____14739
           else ());
          (let prob =
             let uu____14742 =
               let uu____14745 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____14745 in
             FStar_All.pipe_left
               (fun _0_91  -> FStar_TypeChecker_Common.TProb _0_91)
               uu____14742 in
           let g =
             let uu____14750 =
               let uu____14752 = singleton' env prob smt_ok in
               solve_and_commit env uu____14752 (fun uu____14753  -> None) in
             FStar_All.pipe_left (with_guard env prob) uu____14750 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14767 = try_teq true env t1 t2 in
        match uu____14767 with
        | None  ->
            let uu____14769 =
              let uu____14770 =
                let uu____14773 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                let uu____14774 = FStar_TypeChecker_Env.get_range env in
                (uu____14773, uu____14774) in
              FStar_Errors.Error uu____14770 in
            raise uu____14769
        | Some g ->
            ((let uu____14777 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____14777
              then
                let uu____14778 = FStar_Syntax_Print.term_to_string t1 in
                let uu____14779 = FStar_Syntax_Print.term_to_string t2 in
                let uu____14780 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14778
                  uu____14779 uu____14780
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
          (let uu____14796 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14796
           then
             let uu____14797 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____14798 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14797
               uu____14798
           else ());
          (let uu____14800 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____14800 with
           | (prob,x) ->
               let g =
                 let uu____14808 =
                   let uu____14810 = singleton' env prob smt_ok in
                   solve_and_commit env uu____14810
                     (fun uu____14811  -> None) in
                 FStar_All.pipe_left (with_guard env prob) uu____14808 in
               ((let uu____14817 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____14817
                 then
                   let uu____14818 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____14819 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____14820 =
                     let uu____14821 = FStar_Util.must g in
                     guard_to_string env uu____14821 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14818 uu____14819 uu____14820
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
          let uu____14845 = FStar_TypeChecker_Env.get_range env in
          let uu____14846 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.err uu____14845 uu____14846
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____14858 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____14858
         then
           let uu____14859 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____14860 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____14859
             uu____14860
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____14865 =
             let uu____14868 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None uu____14868 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_92  -> FStar_TypeChecker_Common.CProb _0_92) uu____14865 in
         let uu____14871 =
           let uu____14873 = singleton env prob in
           solve_and_commit env uu____14873 (fun uu____14874  -> None) in
         FStar_All.pipe_left (with_guard env prob) uu____14871)
let solve_universe_inequalities':
  FStar_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____14893  ->
        match uu____14893 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Unionfind.rollback tx;
              (let uu____14918 =
                 let uu____14919 =
                   let uu____14922 =
                     let uu____14923 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____14924 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____14923 uu____14924 in
                   let uu____14925 = FStar_TypeChecker_Env.get_range env in
                   (uu____14922, uu____14925) in
                 FStar_Errors.Error uu____14919 in
               raise uu____14918) in
            let equiv v1 v' =
              let uu____14933 =
                let uu____14936 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____14937 = FStar_Syntax_Subst.compress_univ v' in
                (uu____14936, uu____14937) in
              match uu____14933 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Unionfind.equivalent v0 v0'
              | uu____14945 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____14959 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____14959 with
                      | FStar_Syntax_Syntax.U_unif uu____14963 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____14974  ->
                                    match uu____14974 with
                                    | (u,v') ->
                                        let uu____14980 = equiv v1 v' in
                                        if uu____14980
                                        then
                                          let uu____14982 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____14982 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____14992 -> [])) in
            let uu____14995 =
              let wl =
                let uu___180_14998 = empty_worklist env in
                {
                  attempting = (uu___180_14998.attempting);
                  wl_deferred = (uu___180_14998.wl_deferred);
                  ctr = (uu___180_14998.ctr);
                  defer_ok = false;
                  smt_ok = (uu___180_14998.smt_ok);
                  tcenv = (uu___180_14998.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____15005  ->
                      match uu____15005 with
                      | (lb,v1) ->
                          let uu____15010 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____15010 with
                           | USolved wl1 -> ()
                           | uu____15012 -> fail lb v1))) in
            let rec check_ineq uu____15018 =
              match uu____15018 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____15025) -> true
                   | (FStar_Syntax_Syntax.U_succ
                      u0,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name
                      u0,FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif
                      u0,FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Unionfind.equivalent u0 v0
                   | (FStar_Syntax_Syntax.U_name
                      uu____15037,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____15039,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____15044) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____15048,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____15053 -> false) in
            let uu____15056 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____15062  ->
                      match uu____15062 with
                      | (u,v1) ->
                          let uu____15067 = check_ineq (u, v1) in
                          if uu____15067
                          then true
                          else
                            ((let uu____15070 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____15070
                              then
                                let uu____15071 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____15072 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____15071
                                  uu____15072
                              else ());
                             false))) in
            if uu____15056
            then ()
            else
              ((let uu____15076 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____15076
                then
                  ((let uu____15078 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____15078);
                   FStar_Unionfind.rollback tx;
                   (let uu____15084 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____15084))
                else ());
               (let uu____15090 =
                  let uu____15091 =
                    let uu____15094 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____15094) in
                  FStar_Errors.Error uu____15091 in
                raise uu____15090))
let solve_universe_inequalities:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
      FStar_Syntax_Syntax.universe) Prims.list) -> Prims.unit
  =
  fun env  ->
    fun ineqs  ->
      let tx = FStar_Unionfind.new_transaction () in
      solve_universe_inequalities' tx env ineqs; FStar_Unionfind.commit tx
let rec solve_deferred_constraints:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let fail uu____15127 =
        match uu____15127 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____15137 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____15137
       then
         let uu____15138 = wl_to_string wl in
         let uu____15139 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____15138 uu____15139
       else ());
      (let g1 =
         let uu____15151 = solve_and_commit env wl fail in
         match uu____15151 with
         | Some [] ->
             let uu___181_15158 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___181_15158.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_15158.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_15158.FStar_TypeChecker_Env.implicits)
             }
         | uu____15161 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___182_15164 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___182_15164.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___182_15164.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___182_15164.FStar_TypeChecker_Env.implicits)
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
            let uu___183_15190 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___183_15190.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___183_15190.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___183_15190.FStar_TypeChecker_Env.implicits)
            } in
          let uu____15191 =
            let uu____15192 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____15192 in
          if uu____15191
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15198 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____15198
                   then
                     let uu____15199 = FStar_TypeChecker_Env.get_range env in
                     let uu____15200 =
                       let uu____15201 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15201 in
                     FStar_Errors.diag uu____15199 uu____15200
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Simplify] env vc in
                   match check_trivial vc1 with
                   | FStar_TypeChecker_Common.Trivial  -> Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then None
                       else
                         ((let uu____15210 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15210
                           then
                             let uu____15211 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____15212 =
                               let uu____15213 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15213 in
                             FStar_Errors.diag uu____15211 uu____15212
                           else ());
                          (let vcs =
                             let uu____15219 = FStar_Options.use_tactics () in
                             if uu____15219
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)] in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____15233  ->
                                   match uu____15233 with
                                   | (env1,goal) ->
                                       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                         use_env_range_msg env1 goal)));
                          Some ret_g))))
let discharge_guard_no_smt:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15244 = discharge_guard' None env g false in
      match uu____15244 with
      | Some g1 -> g1
      | None  ->
          let uu____15249 =
            let uu____15250 =
              let uu____15253 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____15253) in
            FStar_Errors.Error uu____15250 in
          raise uu____15249
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15260 = discharge_guard' None env g true in
      match uu____15260 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____15280 = FStar_Unionfind.find u in
      match uu____15280 with
      | FStar_Syntax_Syntax.Uvar  -> true
      | uu____15289 -> false in
    let rec until_fixpoint acc implicits =
      let uu____15304 = acc in
      match uu____15304 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____15350 = hd1 in
               (match uu____15350 with
                | (uu____15357,env,u,tm,k,r) ->
                    let uu____15363 = unresolved u in
                    if uu____15363
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm in
                       (let uu____15381 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck") in
                        if uu____15381
                        then
                          let uu____15382 =
                            FStar_Syntax_Print.uvar_to_string u in
                          let uu____15386 =
                            FStar_Syntax_Print.term_to_string tm1 in
                          let uu____15387 =
                            FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____15382 uu____15386 uu____15387
                        else ());
                       (let uu____15389 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___184_15393 = env1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___184_15393.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___184_15393.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___184_15393.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___184_15393.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___184_15393.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___184_15393.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___184_15393.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___184_15393.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___184_15393.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___184_15393.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___184_15393.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___184_15393.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___184_15393.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___184_15393.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___184_15393.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___184_15393.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___184_15393.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___184_15393.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___184_15393.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___184_15393.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___184_15393.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___184_15393.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___184_15393.FStar_TypeChecker_Env.qname_and_index)
                             }) tm1 in
                        match uu____15389 with
                        | (uu____15394,uu____15395,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___185_15398 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___185_15398.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___185_15398.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___185_15398.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____15401 =
                                discharge_guard'
                                  (Some
                                     (fun uu____15405  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____15401 with
                              | Some g3 -> g3
                              | None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
    let uu___186_15420 = g in
    let uu____15421 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___186_15420.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___186_15420.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___186_15420.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____15421
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____15449 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____15449 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15456 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15456
      | (reason,uu____15458,uu____15459,e,t,r)::uu____15463 ->
          let uu____15477 =
            let uu____15478 = FStar_Syntax_Print.term_to_string t in
            let uu____15479 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format3
              "Failed to resolve implicit argument of type '%s' introduced in %s because %s"
              uu____15478 uu____15479 reason in
          FStar_Errors.err r uu____15477
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___187_15486 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___187_15486.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___187_15486.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___187_15486.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15504 = try_teq false env t1 t2 in
        match uu____15504 with
        | None  -> false
        | Some g ->
            let uu____15507 = discharge_guard' None env g false in
            (match uu____15507 with
             | Some uu____15511 -> true
             | None  -> false)