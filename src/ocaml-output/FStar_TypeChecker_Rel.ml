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
        let uv = FStar_Syntax_Unionfind.fresh () in
        match binders with
        | [] ->
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k))
                (Some (k.FStar_Syntax_Syntax.n)) r in
            (uv1, uv1)
        | uu____319 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____334 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____334 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                None r in
            let uu____346 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                (Some (k.FStar_Syntax_Syntax.n)) r in
            (uu____346, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____375 = FStar_Syntax_Util.type_u () in
        match uu____375 with
        | (t_type,u) ->
            let uu____380 =
              let uu____383 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____383 t_type in
            (match uu____380 with
             | (tt,uu____385) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
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
    match projectee with | Success _0 -> true | uu____512 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____526 -> false
let __proj__Failed__item___0:
  solution -> (FStar_TypeChecker_Common.prob* Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0
type variance =
  | COVARIANT
  | CONTRAVARIANT
  | INVARIANT
let uu___is_COVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____543 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____547 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____551 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___105_568  ->
    match uu___105_568 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____581 =
    let uu____582 = FStar_Syntax_Subst.compress t in
    uu____582.FStar_Syntax_Syntax.n in
  match uu____581 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____603 = FStar_Syntax_Print.uvar_to_string u in
      let uu____604 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____603 uu____604
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____607;
         FStar_Syntax_Syntax.pos = uu____608;
         FStar_Syntax_Syntax.vars = uu____609;_},args)
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
    fun uu___106_650  ->
      match uu___106_650 with
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
    fun uu___107_688  ->
      match uu___107_688 with
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
        let uu___138_773 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___138_773.wl_deferred);
          ctr = (uu___138_773.ctr);
          defer_ok = (uu___138_773.defer_ok);
          smt_ok;
          tcenv = (uu___138_773.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___139_798 = empty_worklist env in
  let uu____799 = FStar_List.map FStar_Pervasives.snd g in
  {
    attempting = uu____799;
    wl_deferred = (uu___139_798.wl_deferred);
    ctr = (uu___139_798.ctr);
    defer_ok = false;
    smt_ok = (uu___139_798.smt_ok);
    tcenv = (uu___139_798.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___140_811 = wl in
        {
          attempting = (uu___140_811.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___140_811.ctr);
          defer_ok = (uu___140_811.defer_ok);
          smt_ok = (uu___140_811.smt_ok);
          tcenv = (uu___140_811.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___141_823 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___141_823.wl_deferred);
        ctr = (uu___141_823.ctr);
        defer_ok = (uu___141_823.defer_ok);
        smt_ok = (uu___141_823.smt_ok);
        tcenv = (uu___141_823.tcenv)
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
  fun uu___108_839  ->
    match uu___108_839 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___142_855 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___142_855.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___142_855.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___142_855.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___142_855.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___142_855.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___142_855.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___142_855.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___109_876  ->
    match uu___109_876 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_32  -> FStar_TypeChecker_Common.TProb _0_32)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_33  -> FStar_TypeChecker_Common.CProb _0_33)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___110_892  ->
      match uu___110_892 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___111_895  ->
    match uu___111_895 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___112_904  ->
    match uu___112_904 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___113_914  ->
    match uu___113_914 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___114_924  ->
    match uu___114_924 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun uu___115_935  ->
    match uu___115_935 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___116_946  ->
    match uu___116_946 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___117_955  ->
    match uu___117_955 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_34  -> FStar_TypeChecker_Common.TProb _0_34) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_35  -> FStar_TypeChecker_Common.CProb _0_35) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____969 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____969 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____980  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1030 = next_pid () in
  let uu____1031 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1030;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1031;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1078 = next_pid () in
  let uu____1079 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1078;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1079;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1120 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1120;
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
        let uu____1172 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1172
        then
          let uu____1173 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1174 = prob_to_string env d in
          let uu____1175 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1173 uu____1174 uu____1175 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1180 -> failwith "impossible" in
           let uu____1181 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1189 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1190 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1189, uu____1190)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1194 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1195 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1194, uu____1195) in
           match uu____1181 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___118_1204  ->
            match uu___118_1204 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1212 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1214),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___119_1227  ->
           match uu___119_1227 with
           | UNIV uu____1229 -> None
           | TERM ((u,uu____1233),t) ->
               let uu____1237 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1237 then Some t else None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___120_1249  ->
           match uu___120_1249 with
           | UNIV (u',t) ->
               let uu____1253 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1253 then Some t else None
           | uu____1256 -> None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1263 =
        let uu____1264 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1264 in
      FStar_Syntax_Subst.compress uu____1263
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1271 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1271
let norm_arg env t = let uu____1290 = sn env (fst t) in (uu____1290, (snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1307  ->
              match uu____1307 with
              | (x,imp) ->
                  let uu____1314 =
                    let uu___143_1315 = x in
                    let uu____1316 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___143_1315.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___143_1315.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1316
                    } in
                  (uu____1314, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1331 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1331
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1334 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1334
        | uu____1336 -> u2 in
      let uu____1337 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1337
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1444 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____1444 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1456;
               FStar_Syntax_Syntax.pos = uu____1457;
               FStar_Syntax_Syntax.vars = uu____1458;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1479 =
                 let uu____1480 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1481 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1480
                   uu____1481 in
               failwith uu____1479)
    | FStar_Syntax_Syntax.Tm_uinst uu____1491 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1518 =
             let uu____1519 = FStar_Syntax_Subst.compress t1' in
             uu____1519.FStar_Syntax_Syntax.n in
           match uu____1518 with
           | FStar_Syntax_Syntax.Tm_refine uu____1531 -> aux true t1'
           | uu____1536 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1548 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1571 =
             let uu____1572 = FStar_Syntax_Subst.compress t1' in
             uu____1572.FStar_Syntax_Syntax.n in
           match uu____1571 with
           | FStar_Syntax_Syntax.Tm_refine uu____1584 -> aux true t1'
           | uu____1589 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_app uu____1601 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1633 =
             let uu____1634 = FStar_Syntax_Subst.compress t1' in
             uu____1634.FStar_Syntax_Syntax.n in
           match uu____1633 with
           | FStar_Syntax_Syntax.Tm_refine uu____1646 -> aux true t1'
           | uu____1651 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_type uu____1663 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_constant uu____1675 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_name uu____1687 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1699 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1711 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_abs uu____1730 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1756 -> (t11, None)
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
    fun uu___121_2076  ->
      match uu___121_2076 with
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
                let uu____2183 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2183)
              else
                (let uu____2197 = FStar_Syntax_Util.abs_formals t in
                 match uu____2197 with
                 | (ys',t1,uu____2218) ->
                     let uu____2231 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2231))
          | uu____2252 ->
              let uu____2253 =
                let uu____2259 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____2259) in
              ((ys, t), uu____2253) in
        match uu____2131 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2314 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2314 c in
               let uu____2316 =
                 let uu____2323 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_36  -> FStar_Util.Inl _0_36) in
                 FStar_All.pipe_right uu____2323 (fun _0_37  -> Some _0_37) in
               FStar_Syntax_Util.abs ys1 t1 uu____2316)
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
            let uu____2374 = p_guard prob in
            match uu____2374 with
            | (uu____2377,uv) ->
                ((let uu____2380 =
                    let uu____2381 = FStar_Syntax_Subst.compress uv in
                    uu____2381.FStar_Syntax_Syntax.n in
                  match uu____2380 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2405 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2405
                        then
                          let uu____2406 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2407 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2408 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2406
                            uu____2407 uu____2408
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2410 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___144_2413 = wl in
                  {
                    attempting = (uu___144_2413.attempting);
                    wl_deferred = (uu___144_2413.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___144_2413.defer_ok);
                    smt_ok = (uu___144_2413.smt_ok);
                    tcenv = (uu___144_2413.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2426 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2426
         then
           let uu____2427 = FStar_Util.string_of_int pid in
           let uu____2428 =
             let uu____2429 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2429 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2427 uu____2428
         else ());
        commit sol;
        (let uu___145_2434 = wl in
         {
           attempting = (uu___145_2434.attempting);
           wl_deferred = (uu___145_2434.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___145_2434.defer_ok);
           smt_ok = (uu___145_2434.smt_ok);
           tcenv = (uu___145_2434.tcenv)
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
            | (uu____2463,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2471 = FStar_Syntax_Util.mk_conj t1 f in
                Some uu____2471 in
          (let uu____2477 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2477
           then
             let uu____2478 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2479 =
               let uu____2480 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2480 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2478 uu____2479
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2505 =
    let uu____2509 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2509 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2505
    (FStar_Util.for_some
       (fun uu____2526  ->
          match uu____2526 with
          | (uv,uu____2530) -> FStar_Syntax_Unionfind.equiv uv (fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2563 = occurs wl uk t in Prims.op_Negation uu____2563 in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2568 =
         let uu____2569 = FStar_Syntax_Print.uvar_to_string (fst uk) in
         let uu____2570 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2569 uu____2570 in
       Some uu____2568) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2618 = occurs_check env wl uk t in
  match uu____2618 with
  | (occurs_ok,msg) ->
      let uu____2635 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2635, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2699 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2723  ->
            fun uu____2724  ->
              match (uu____2723, uu____2724) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2767 =
                    let uu____2768 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2768 in
                  if uu____2767
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2782 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2782
                     then
                       let uu____2789 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____2789)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2699 with | (isect,uu____2811) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2860  ->
          fun uu____2861  ->
            match (uu____2860, uu____2861) with
            | ((a,uu____2871),(b,uu____2873)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2917 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2923  ->
                match uu____2923 with
                | (b,uu____2927) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____2917 then None else Some (a, (snd hd1))
  | uu____2936 -> None
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
            let uu____2979 = pat_var_opt env seen hd1 in
            (match uu____2979 with
             | None  ->
                 ((let uu____2987 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____2987
                   then
                     let uu____2988 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____2988
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3000 =
      let uu____3001 = FStar_Syntax_Subst.compress t in
      uu____3001.FStar_Syntax_Syntax.n in
    match uu____3000 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3004 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3015;
           FStar_Syntax_Syntax.tk = uu____3016;
           FStar_Syntax_Syntax.pos = uu____3017;
           FStar_Syntax_Syntax.vars = uu____3018;_},uu____3019)
        -> true
    | uu____3044 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3114;
         FStar_Syntax_Syntax.pos = uu____3115;
         FStar_Syntax_Syntax.vars = uu____3116;_},args)
      -> (t, uv, k, args)
  | uu____3163 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____3221 = destruct_flex_t t in
  match uu____3221 with
  | (t1,uv,k,args) ->
      let uu____3297 = pat_vars env [] args in
      (match uu____3297 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3359 -> ((t1, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth option*
  FStar_Syntax_Syntax.delta_depth option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3411 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth option* FStar_Syntax_Syntax.delta_depth
      option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3434 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3438 -> false
let head_match: match_result -> match_result =
  fun uu___122_3441  ->
    match uu___122_3441 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3450 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3463 ->
          let uu____3464 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3464 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3474 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3488 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3494 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> None
      | FStar_Syntax_Syntax.Tm_bvar uu____3516 -> None
      | FStar_Syntax_Syntax.Tm_name uu____3517 -> None
      | FStar_Syntax_Syntax.Tm_uvar uu____3518 -> None
      | FStar_Syntax_Syntax.Tm_let uu____3529 -> None
      | FStar_Syntax_Syntax.Tm_match uu____3537 -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3554) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3560,uu____3561) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3591) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3606;
             FStar_Syntax_Syntax.index = uu____3607;
             FStar_Syntax_Syntax.sort = t2;_},uu____3609)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3616 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3617 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3618 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3626 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3642 = fv_delta_depth env fv in Some uu____3642
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
            let uu____3661 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3661
            then FullMatch
            else
              (let uu____3663 =
                 let uu____3668 =
                   let uu____3670 = fv_delta_depth env f in Some uu____3670 in
                 let uu____3671 =
                   let uu____3673 = fv_delta_depth env g in Some uu____3673 in
                 (uu____3668, uu____3671) in
               MisMatch uu____3663)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3677),FStar_Syntax_Syntax.Tm_uinst (g,uu____3679)) ->
            let uu____3688 = head_matches env f g in
            FStar_All.pipe_right uu____3688 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3695),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3697)) ->
            let uu____3730 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____3730 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3735),FStar_Syntax_Syntax.Tm_refine (y,uu____3737)) ->
            let uu____3746 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3746 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3748),uu____3749) ->
            let uu____3754 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3754 head_match
        | (uu____3755,FStar_Syntax_Syntax.Tm_refine (x,uu____3757)) ->
            let uu____3762 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3762 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3763,FStar_Syntax_Syntax.Tm_type
           uu____3764) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3765,FStar_Syntax_Syntax.Tm_arrow uu____3766) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3782),FStar_Syntax_Syntax.Tm_app (head',uu____3784))
            ->
            let uu____3813 = head_matches env head1 head' in
            FStar_All.pipe_right uu____3813 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3815),uu____3816) ->
            let uu____3831 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____3831 head_match
        | (uu____3832,FStar_Syntax_Syntax.Tm_app (head1,uu____3834)) ->
            let uu____3849 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____3849 head_match
        | uu____3850 ->
            let uu____3853 =
              let uu____3858 = delta_depth_of_term env t11 in
              let uu____3860 = delta_depth_of_term env t21 in
              (uu____3858, uu____3860) in
            MisMatch uu____3853
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3896 = FStar_Syntax_Util.head_and_args t in
    match uu____3896 with
    | (head1,uu____3908) ->
        let uu____3923 =
          let uu____3924 = FStar_Syntax_Util.un_uinst head1 in
          uu____3924.FStar_Syntax_Syntax.n in
        (match uu____3923 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3929 =
               let uu____3930 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____3930 FStar_Option.isSome in
             if uu____3929
             then
               let uu____3944 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____3944 (fun _0_38  -> Some _0_38)
             else None
         | uu____3947 -> None) in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None)) in
  let fail r = (r, None) in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21 in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),uu____4015) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4025 =
             let uu____4030 = maybe_inline t11 in
             let uu____4032 = maybe_inline t21 in (uu____4030, uu____4032) in
           match uu____4025 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (uu____4053,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4063 =
             let uu____4068 = maybe_inline t11 in
             let uu____4070 = maybe_inline t21 in (uu____4068, uu____4070) in
           match uu____4063 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____4095 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____4095 with
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
        let uu____4110 =
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
             let uu____4118 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____4118)) in
        (match uu____4110 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4126 -> fail r
    | uu____4131 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4156 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4186 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4201 = FStar_Syntax_Util.type_u () in
      match uu____4201 with
      | (t,uu____4205) ->
          let uu____4206 = new_uvar r binders t in fst uu____4206
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4215 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____4215 FStar_Pervasives.fst
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
        let uu____4257 = head_matches env t1 t' in
        match uu____4257 with
        | MisMatch uu____4258 -> false
        | uu____4263 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4323,imp),T (t2,uu____4326)) -> (t2, imp)
                     | uu____4343 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4383  ->
                    match uu____4383 with
                    | (t2,uu____4391) ->
                        (None, INVARIANT, (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let fail uu____4424 = failwith "Bad reconstruction" in
          let uu____4425 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____4425 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4478))::tcs2) ->
                       aux
                         (((let uu___146_4500 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_4500.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_4500.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4510 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___123_4541 =
                 match uu___123_4541 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4604 = decompose1 [] bs1 in
               (rebuild, matches, uu____4604))
      | uu____4632 ->
          let rebuild uu___124_4637 =
            match uu___124_4637 with
            | [] -> t1
            | uu____4639 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___125_4658  ->
    match uu___125_4658 with
    | T (t,uu____4660) -> t
    | uu____4669 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___126_4672  ->
    match uu___126_4672 with
    | T (t,uu____4674) -> FStar_Syntax_Syntax.as_arg t
    | uu____4683 -> failwith "Impossible"
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
              | (uu____4752,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4771 = new_uvar r scope1 k in
                  (match uu____4771 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4783 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args)) None r in
                       let uu____4798 =
                         let uu____4799 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_39  ->
                              FStar_TypeChecker_Common.TProb _0_39)
                           uu____4799 in
                       ((T (gi_xs, mk_kind)), uu____4798))
              | (uu____4808,uu____4809,C uu____4810) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4897 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4908;
                         FStar_Syntax_Syntax.pos = uu____4909;
                         FStar_Syntax_Syntax.vars = uu____4910;_})
                        ->
                        let uu____4925 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4925 with
                         | (T (gi_xs,uu____4941),prob) ->
                             let uu____4951 =
                               let uu____4952 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_40  -> C _0_40)
                                 uu____4952 in
                             (uu____4951, [prob])
                         | uu____4954 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4964;
                         FStar_Syntax_Syntax.pos = uu____4965;
                         FStar_Syntax_Syntax.vars = uu____4966;_})
                        ->
                        let uu____4981 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4981 with
                         | (T (gi_xs,uu____4997),prob) ->
                             let uu____5007 =
                               let uu____5008 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_41  -> C _0_41)
                                 uu____5008 in
                             (uu____5007, [prob])
                         | uu____5010 -> failwith "impossible")
                    | (uu____5016,uu____5017,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____5019;
                         FStar_Syntax_Syntax.pos = uu____5020;
                         FStar_Syntax_Syntax.vars = uu____5021;_})
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
                        let uu____5095 =
                          let uu____5100 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____5100 FStar_List.unzip in
                        (match uu____5095 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5129 =
                                 let uu____5130 =
                                   let uu____5133 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____5133 un_T in
                                 let uu____5134 =
                                   let uu____5140 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____5140
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5130;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5134;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5129 in
                             ((C gi_xs), sub_probs))
                    | uu____5145 ->
                        let uu____5152 = sub_prob scope1 args q in
                        (match uu____5152 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____4897 with
                   | (tc,probs) ->
                       let uu____5170 =
                         match q with
                         | (Some b,uu____5196,uu____5197) ->
                             let uu____5205 =
                               let uu____5209 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____5209 :: args in
                             ((Some b), (b :: scope1), uu____5205)
                         | uu____5227 -> (None, scope1, args) in
                       (match uu____5170 with
                        | (bopt,scope2,args1) ->
                            let uu____5270 = aux scope2 args1 qs2 in
                            (match uu____5270 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____5291 =
                                         let uu____5293 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         f :: uu____5293 in
                                       FStar_Syntax_Util.mk_conj_l uu____5291
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (fst b).FStar_Syntax_Syntax.sort in
                                       let uu____5306 =
                                         let uu____5308 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (fst b) f in
                                         let uu____5309 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         uu____5308 :: uu____5309 in
                                       FStar_Syntax_Util.mk_conj_l uu____5306 in
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
  let uu___147_5362 = p in
  let uu____5365 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____5366 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___147_5362.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5365;
    FStar_TypeChecker_Common.relation =
      (uu___147_5362.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5366;
    FStar_TypeChecker_Common.element =
      (uu___147_5362.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___147_5362.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___147_5362.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___147_5362.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___147_5362.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___147_5362.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5376 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____5376
            (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
      | FStar_TypeChecker_Common.CProb uu____5381 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5395 = compress_prob wl pr in
        FStar_All.pipe_right uu____5395 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5401 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____5401 with
           | (lh,uu____5414) ->
               let uu____5429 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____5429 with
                | (rh,uu____5442) ->
                    let uu____5457 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5466,FStar_Syntax_Syntax.Tm_uvar uu____5467)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5490,uu____5491)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5504,FStar_Syntax_Syntax.Tm_uvar uu____5505)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5518,uu____5519)
                          ->
                          let uu____5530 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5530 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5570 ->
                                    let rank =
                                      let uu____5577 = is_top_level_prob prob in
                                      if uu____5577
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5579 =
                                      let uu___148_5582 = tp in
                                      let uu____5585 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___148_5582.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___148_5582.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___148_5582.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5585;
                                        FStar_TypeChecker_Common.element =
                                          (uu___148_5582.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___148_5582.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___148_5582.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___148_5582.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___148_5582.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___148_5582.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5579)))
                      | (uu____5595,FStar_Syntax_Syntax.Tm_uvar uu____5596)
                          ->
                          let uu____5607 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5607 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5647 ->
                                    let uu____5653 =
                                      let uu___149_5658 = tp in
                                      let uu____5661 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_5658.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5661;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_5658.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___149_5658.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_5658.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_5658.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_5658.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_5658.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_5658.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_5658.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5653)))
                      | (uu____5677,uu____5678) -> (rigid_rigid, tp) in
                    (match uu____5457 with
                     | (rank,tp1) ->
                         let uu____5689 =
                           FStar_All.pipe_right
                             (let uu___150_5692 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___150_5692.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___150_5692.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___150_5692.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___150_5692.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___150_5692.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___150_5692.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___150_5692.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___150_5692.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___150_5692.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_43  ->
                                FStar_TypeChecker_Common.TProb _0_43) in
                         (rank, uu____5689))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5698 =
            FStar_All.pipe_right
              (let uu___151_5701 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___151_5701.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___151_5701.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___151_5701.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___151_5701.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___151_5701.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___151_5701.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___151_5701.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___151_5701.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___151_5701.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) in
          (rigid_rigid, uu____5698)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob option* FStar_TypeChecker_Common.prob
      Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____5733 probs =
      match uu____5733 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5763 = rank wl hd1 in
               (match uu____5763 with
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
    match projectee with | UDeferred _0 -> true | uu____5828 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5840 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5852 -> false
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
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____5895 -> false)))
            | uu____5896 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____5939 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____5939 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5942 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____5948 =
                     let uu____5949 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____5950 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5949
                       uu____5950 in
                   UFailed uu____5948)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5966 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5966 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5984 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5984 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____5987 ->
                let uu____5990 =
                  let uu____5991 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____5992 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5991
                    uu____5992 msg in
                UFailed uu____5990 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____5993,uu____5994) ->
              let uu____5995 =
                let uu____5996 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5997 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5996 uu____5997 in
              failwith uu____5995
          | (FStar_Syntax_Syntax.U_unknown ,uu____5998) ->
              let uu____5999 =
                let uu____6000 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6001 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6000 uu____6001 in
              failwith uu____5999
          | (uu____6002,FStar_Syntax_Syntax.U_bvar uu____6003) ->
              let uu____6004 =
                let uu____6005 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6006 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6005 uu____6006 in
              failwith uu____6004
          | (uu____6007,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____6008 =
                let uu____6009 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6010 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6009 uu____6010 in
              failwith uu____6008
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____6026 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____6026
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____6040 = occurs_univ v1 u3 in
              if uu____6040
              then
                let uu____6041 =
                  let uu____6042 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6043 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6042 uu____6043 in
                try_umax_components u11 u21 uu____6041
              else
                (let uu____6045 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6045)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____6057 = occurs_univ v1 u3 in
              if uu____6057
              then
                let uu____6058 =
                  let uu____6059 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6060 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6059 uu____6060 in
                try_umax_components u11 u21 uu____6058
              else
                (let uu____6062 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6062)
          | (FStar_Syntax_Syntax.U_max uu____6067,uu____6068) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6073 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6073
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____6075,FStar_Syntax_Syntax.U_max uu____6076) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6081 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6081
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6083,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6084,FStar_Syntax_Syntax.U_name
             uu____6085) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6086) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6087) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6088,FStar_Syntax_Syntax.U_succ
             uu____6089) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6090,FStar_Syntax_Syntax.U_zero
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
  let uu____6152 = bc1 in
  match uu____6152 with
  | (bs1,mk_cod1) ->
      let uu____6177 = bc2 in
      (match uu____6177 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6224 = FStar_Util.first_N n1 bs in
             match uu____6224 with
             | (bs3,rest) ->
                 let uu____6238 = mk_cod rest in (bs3, uu____6238) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____6256 =
               let uu____6260 = mk_cod1 [] in (bs1, uu____6260) in
             let uu____6262 =
               let uu____6266 = mk_cod2 [] in (bs2, uu____6266) in
             (uu____6256, uu____6262)
           else
             if l1 > l2
             then
               (let uu____6288 = curry l2 bs1 mk_cod1 in
                let uu____6295 =
                  let uu____6299 = mk_cod2 [] in (bs2, uu____6299) in
                (uu____6288, uu____6295))
             else
               (let uu____6308 =
                  let uu____6312 = mk_cod1 [] in (bs1, uu____6312) in
                let uu____6314 = curry l1 bs2 mk_cod2 in
                (uu____6308, uu____6314)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6418 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____6418
       then
         let uu____6419 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6419
       else ());
      (let uu____6421 = next_prob probs in
       match uu____6421 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___152_6434 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___152_6434.wl_deferred);
               ctr = (uu___152_6434.ctr);
               defer_ok = (uu___152_6434.defer_ok);
               smt_ok = (uu___152_6434.smt_ok);
               tcenv = (uu___152_6434.tcenv)
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
                  let uu____6441 = solve_flex_rigid_join env tp probs1 in
                  (match uu____6441 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6445 = solve_rigid_flex_meet env tp probs1 in
                     match uu____6445 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____6449,uu____6450) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6459 ->
                let uu____6464 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6492  ->
                          match uu____6492 with
                          | (c,uu____6497,uu____6498) -> c < probs.ctr)) in
                (match uu____6464 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6520 =
                            FStar_List.map
                              (fun uu____6526  ->
                                 match uu____6526 with
                                 | (uu____6532,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____6520
                      | uu____6535 ->
                          let uu____6540 =
                            let uu___153_6541 = probs in
                            let uu____6542 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6551  ->
                                      match uu____6551 with
                                      | (uu____6555,uu____6556,y) -> y)) in
                            {
                              attempting = uu____6542;
                              wl_deferred = rest;
                              ctr = (uu___153_6541.ctr);
                              defer_ok = (uu___153_6541.defer_ok);
                              smt_ok = (uu___153_6541.smt_ok);
                              tcenv = (uu___153_6541.tcenv)
                            } in
                          solve env uu____6540))))
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
            let uu____6563 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____6563 with
            | USolved wl1 ->
                let uu____6565 = solve_prob orig None [] wl1 in
                solve env uu____6565
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
                  let uu____6599 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6599 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6602 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6610;
                  FStar_Syntax_Syntax.pos = uu____6611;
                  FStar_Syntax_Syntax.vars = uu____6612;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6615;
                  FStar_Syntax_Syntax.pos = uu____6616;
                  FStar_Syntax_Syntax.vars = uu____6617;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6629,uu____6630) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6635,FStar_Syntax_Syntax.Tm_uinst uu____6636) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6641 -> USolved wl
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
            ((let uu____6649 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6649
              then
                let uu____6650 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6650 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6658 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6658
         then
           let uu____6659 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6659
         else ());
        (let uu____6661 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6661 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6703 = head_matches_delta env () t1 t2 in
               match uu____6703 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6725 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6751 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6760 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____6761 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____6760, uu____6761)
                          | None  ->
                              let uu____6764 = FStar_Syntax_Subst.compress t1 in
                              let uu____6765 = FStar_Syntax_Subst.compress t2 in
                              (uu____6764, uu____6765) in
                        (match uu____6751 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6787 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_45  ->
                                    FStar_TypeChecker_Common.TProb _0_45)
                                 uu____6787 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6810 =
                                    let uu____6816 =
                                      let uu____6819 =
                                        let uu____6822 =
                                          let uu____6823 =
                                            let uu____6828 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____6828) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6823 in
                                        FStar_Syntax_Syntax.mk uu____6822 in
                                      uu____6819 None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____6841 =
                                      let uu____6843 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____6843] in
                                    (uu____6816, uu____6841) in
                                  Some uu____6810
                              | (uu____6852,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6854)) ->
                                  let uu____6859 =
                                    let uu____6863 =
                                      let uu____6865 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____6865] in
                                    (t11, uu____6863) in
                                  Some uu____6859
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6871),uu____6872) ->
                                  let uu____6877 =
                                    let uu____6881 =
                                      let uu____6883 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____6883] in
                                    (t21, uu____6881) in
                                  Some uu____6877
                              | uu____6888 ->
                                  let uu____6891 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____6891 with
                                   | (head1,uu____6906) ->
                                       let uu____6921 =
                                         let uu____6922 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____6922.FStar_Syntax_Syntax.n in
                                       (match uu____6921 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6929;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6931;_}
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
                                        | uu____6940 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6949) ->
                  let uu____6966 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___127_6975  ->
                            match uu___127_6975 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6980 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____6980 with
                                      | (u',uu____6991) ->
                                          let uu____7006 =
                                            let uu____7007 = whnf env u' in
                                            uu____7007.FStar_Syntax_Syntax.n in
                                          (match uu____7006 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____7011) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____7028 -> false))
                                 | uu____7029 -> false)
                            | uu____7031 -> false)) in
                  (match uu____6966 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____7052 tps =
                         match uu____7052 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7079 =
                                    let uu____7084 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____7084 in
                                  (match uu____7079 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____7103 -> None) in
                       let uu____7108 =
                         let uu____7113 =
                           let uu____7117 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____7117, []) in
                         make_lower_bound uu____7113 lower_bounds in
                       (match uu____7108 with
                        | None  ->
                            ((let uu____7124 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7124
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
                            ((let uu____7137 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7137
                              then
                                let wl' =
                                  let uu___154_7139 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___154_7139.wl_deferred);
                                    ctr = (uu___154_7139.ctr);
                                    defer_ok = (uu___154_7139.defer_ok);
                                    smt_ok = (uu___154_7139.smt_ok);
                                    tcenv = (uu___154_7139.tcenv)
                                  } in
                                let uu____7140 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7140
                              else ());
                             (let uu____7142 =
                                solve_t env eq_prob
                                  (let uu___155_7143 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___155_7143.wl_deferred);
                                     ctr = (uu___155_7143.ctr);
                                     defer_ok = (uu___155_7143.defer_ok);
                                     smt_ok = (uu___155_7143.smt_ok);
                                     tcenv = (uu___155_7143.tcenv)
                                   }) in
                              match uu____7142 with
                              | Success uu____7145 ->
                                  let wl1 =
                                    let uu___156_7147 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___156_7147.wl_deferred);
                                      ctr = (uu___156_7147.ctr);
                                      defer_ok = (uu___156_7147.defer_ok);
                                      smt_ok = (uu___156_7147.smt_ok);
                                      tcenv = (uu___156_7147.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1 in
                                  let uu____7149 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds in
                                  Some wl2
                              | uu____7152 -> None))))
              | uu____7153 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7160 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____7160
         then
           let uu____7161 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7161
         else ());
        (let uu____7163 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____7163 with
         | (u,args) ->
             let uu____7190 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____7190 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____7221 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____7221 with
                    | (h1,args1) ->
                        let uu____7249 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____7249 with
                         | (h2,uu____7262) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7281 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____7281
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7294 =
                                          let uu____7296 =
                                            let uu____7297 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_46  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_46) uu____7297 in
                                          [uu____7296] in
                                        Some uu____7294))
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
                                       (let uu____7319 =
                                          let uu____7321 =
                                            let uu____7322 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_47  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_47) uu____7322 in
                                          [uu____7321] in
                                        Some uu____7319))
                                  else None
                              | uu____7330 -> None)) in
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
                             let uu____7396 =
                               let uu____7402 =
                                 let uu____7405 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____7405 in
                               (uu____7402, m1) in
                             Some uu____7396)
                    | (uu____7414,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7416)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7448),uu____7449) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____7480 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7514) ->
                       let uu____7531 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___128_7540  ->
                                 match uu___128_7540 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____7545 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____7545 with
                                           | (u',uu____7556) ->
                                               let uu____7571 =
                                                 let uu____7572 = whnf env u' in
                                                 uu____7572.FStar_Syntax_Syntax.n in
                                               (match uu____7571 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7576) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____7593 -> false))
                                      | uu____7594 -> false)
                                 | uu____7596 -> false)) in
                       (match uu____7531 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7621 tps =
                              match uu____7621 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7662 =
                                         let uu____7669 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7669 in
                                       (match uu____7662 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7704 -> None) in
                            let uu____7711 =
                              let uu____7718 =
                                let uu____7724 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7724, []) in
                              make_upper_bound uu____7718 upper_bounds in
                            (match uu____7711 with
                             | None  ->
                                 ((let uu____7733 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7733
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
                                 ((let uu____7752 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7752
                                   then
                                     let wl' =
                                       let uu___157_7754 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___157_7754.wl_deferred);
                                         ctr = (uu___157_7754.ctr);
                                         defer_ok = (uu___157_7754.defer_ok);
                                         smt_ok = (uu___157_7754.smt_ok);
                                         tcenv = (uu___157_7754.tcenv)
                                       } in
                                     let uu____7755 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7755
                                   else ());
                                  (let uu____7757 =
                                     solve_t env eq_prob
                                       (let uu___158_7758 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___158_7758.wl_deferred);
                                          ctr = (uu___158_7758.ctr);
                                          defer_ok = (uu___158_7758.defer_ok);
                                          smt_ok = (uu___158_7758.smt_ok);
                                          tcenv = (uu___158_7758.tcenv)
                                        }) in
                                   match uu____7757 with
                                   | Success uu____7760 ->
                                       let wl1 =
                                         let uu___159_7762 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___159_7762.wl_deferred);
                                           ctr = (uu___159_7762.ctr);
                                           defer_ok =
                                             (uu___159_7762.defer_ok);
                                           smt_ok = (uu___159_7762.smt_ok);
                                           tcenv = (uu___159_7762.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1 in
                                       let uu____7764 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds in
                                       Some wl2
                                   | uu____7767 -> None))))
                   | uu____7768 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____7833 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____7833
                      then
                        let uu____7834 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7834
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___160_7866 = hd1 in
                      let uu____7867 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___160_7866.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___160_7866.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7867
                      } in
                    let hd21 =
                      let uu___161_7871 = hd2 in
                      let uu____7872 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_7871.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_7871.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7872
                      } in
                    let prob =
                      let uu____7876 =
                        let uu____7879 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7879 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_48  -> FStar_TypeChecker_Common.TProb _0_48)
                        uu____7876 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____7887 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7887 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____7890 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____7890 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7908 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives.fst in
                           let uu____7911 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____7908 uu____7911 in
                         ((let uu____7917 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____7917
                           then
                             let uu____7918 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____7919 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7918 uu____7919
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7934 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____7940 = aux scope env [] bs1 bs2 in
              match uu____7940 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7956 = compress_tprob wl problem in
        solve_t' env uu____7956 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7989 = head_matches_delta env1 wl1 t1 t2 in
          match uu____7989 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____8006,uu____8007) ->
                   let may_relate head3 =
                     let uu____8022 =
                       let uu____8023 = FStar_Syntax_Util.un_uinst head3 in
                       uu____8023.FStar_Syntax_Syntax.n in
                     match uu____8022 with
                     | FStar_Syntax_Syntax.Tm_name uu____8026 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____8027 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____8044 -> false in
                   let uu____8045 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____8045
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
                                let uu____8062 =
                                  let uu____8063 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____8063 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____8062 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____8065 = solve_prob orig (Some guard) [] wl1 in
                     solve env1 uu____8065
                   else giveup env1 "head mismatch" orig
               | (uu____8067,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___162_8075 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___162_8075.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___162_8075.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___162_8075.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___162_8075.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___162_8075.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___162_8075.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___162_8075.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___162_8075.FStar_TypeChecker_Common.rank)
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
                                let uu____8155 =
                                  let uu____8156 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____8157 = args_to_string args1 in
                                  let uu____8158 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____8159 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8156 uu____8157 uu____8158
                                    uu____8159 in
                                giveup env1 uu____8155 orig
                              else
                                (let uu____8161 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8164 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____8164 = FStar_Syntax_Util.Equal) in
                                 if uu____8161
                                 then
                                   let uu____8165 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____8165 with
                                   | USolved wl2 ->
                                       let uu____8167 =
                                         solve_prob orig None [] wl2 in
                                       solve env1 uu____8167
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8171 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____8171 with
                                    | (base1,refinement1) ->
                                        let uu____8197 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____8197 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____8251 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____8251 with
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
                                                           (fun uu____8261 
                                                              ->
                                                              fun uu____8262 
                                                                ->
                                                                match 
                                                                  (uu____8261,
                                                                    uu____8262)
                                                                with
                                                                | ((a,uu____8272),
                                                                   (a',uu____8274))
                                                                    ->
                                                                    let uu____8279
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
                                                                    uu____8279)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____8285 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8285 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8289 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___163_8322 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___163_8322.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___163_8322.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___163_8322.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___163_8322.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___163_8322.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___163_8322.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___163_8322.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___163_8322.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____8342 = p in
          match uu____8342 with
          | (((u,k),xs,c),ps,(h,uu____8353,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8402 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____8402 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8416 = h gs_xs in
                     let uu____8417 =
                       let uu____8424 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_50  -> FStar_Util.Inl _0_50) in
                       FStar_All.pipe_right uu____8424
                         (fun _0_51  -> Some _0_51) in
                     FStar_Syntax_Util.abs xs1 uu____8416 uu____8417 in
                   ((let uu____8455 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8455
                     then
                       let uu____8456 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____8457 = FStar_Syntax_Print.comp_to_string c in
                       let uu____8458 = FStar_Syntax_Print.term_to_string im in
                       let uu____8459 = FStar_Syntax_Print.tag_of_term im in
                       let uu____8460 =
                         let uu____8461 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____8461
                           (FStar_String.concat ", ") in
                       let uu____8464 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8456 uu____8457 uu____8458 uu____8459
                         uu____8460 uu____8464
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___129_8482 =
          match uu___129_8482 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____8511 = p in
          match uu____8511 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8569 = FStar_List.nth ps i in
              (match uu____8569 with
               | (pi,uu____8572) ->
                   let uu____8577 = FStar_List.nth xs i in
                   (match uu____8577 with
                    | (xi,uu____8584) ->
                        let rec gs k =
                          let uu____8593 = FStar_Syntax_Util.arrow_formals k in
                          match uu____8593 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8645)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8653 = new_uvar r xs k_a in
                                    (match uu____8653 with
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
                                         let uu____8672 = aux subst2 tl1 in
                                         (match uu____8672 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8687 =
                                                let uu____8689 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8689 :: gi_xs' in
                                              let uu____8690 =
                                                let uu____8692 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8692 :: gi_ps' in
                                              (uu____8687, uu____8690))) in
                              aux [] bs in
                        let uu____8695 =
                          let uu____8696 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8696 in
                        if uu____8695
                        then None
                        else
                          (let uu____8699 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8699 with
                           | (g_xs,uu____8706) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8713 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r in
                                 let uu____8718 =
                                   let uu____8725 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_52  -> FStar_Util.Inl _0_52) in
                                   FStar_All.pipe_right uu____8725
                                     (fun _0_53  -> Some _0_53) in
                                 FStar_Syntax_Util.abs xs uu____8713
                                   uu____8718 in
                               let sub1 =
                                 let uu____8756 =
                                   let uu____8759 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let uu____8766 =
                                     let uu____8769 =
                                       FStar_List.map
                                         (fun uu____8775  ->
                                            match uu____8775 with
                                            | (uu____8780,uu____8781,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____8769 in
                                   mk_problem (p_scope orig) orig uu____8759
                                     (p_rel orig) uu____8766 None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_54  ->
                                      FStar_TypeChecker_Common.TProb _0_54)
                                   uu____8756 in
                               ((let uu____8791 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____8791
                                 then
                                   let uu____8792 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____8793 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8792 uu____8793
                                 else ());
                                (let wl2 =
                                   let uu____8796 =
                                     let uu____8798 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives.fst (p_guard sub1) in
                                     Some uu____8798 in
                                   solve_prob orig uu____8796
                                     [TERM (u, proj)] wl1 in
                                 let uu____8803 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_55  -> Some _0_55) uu____8803))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8827 = lhs in
          match uu____8827 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8850 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____8850 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8872 =
                        let uu____8898 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____8898) in
                      Some uu____8872
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____8981 =
                           let uu____8985 =
                             let uu____8986 = FStar_Syntax_Subst.compress k in
                             uu____8986.FStar_Syntax_Syntax.n in
                           (uu____8985, args) in
                         match uu____8981 with
                         | (uu____8993,[]) ->
                             let uu____8995 =
                               let uu____9001 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____9001) in
                             Some uu____8995
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____9012,uu____9013) ->
                             let uu____9026 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9026 with
                              | (uv1,uv_args) ->
                                  let uu____9055 =
                                    let uu____9056 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9056.FStar_Syntax_Syntax.n in
                                  (match uu____9055 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9063) ->
                                       let uu____9080 =
                                         pat_vars env [] uv_args in
                                       (match uu____9080 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9094  ->
                                                      let uu____9095 =
                                                        let uu____9096 =
                                                          let uu____9097 =
                                                            let uu____9100 =
                                                              let uu____9101
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9101
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9100 in
                                                          fst uu____9097 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9096 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9095)) in
                                            let c1 =
                                              let uu____9107 =
                                                let uu____9108 =
                                                  let uu____9111 =
                                                    let uu____9112 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9112
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9111 in
                                                fst uu____9108 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9107 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9121 =
                                                let uu____9128 =
                                                  let uu____9134 =
                                                    let uu____9135 =
                                                      let uu____9138 =
                                                        let uu____9139 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9139
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9138 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9135 in
                                                  FStar_Util.Inl uu____9134 in
                                                Some uu____9128 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9121 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9159 -> None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9162,uu____9163)
                             ->
                             let uu____9175 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9175 with
                              | (uv1,uv_args) ->
                                  let uu____9204 =
                                    let uu____9205 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9205.FStar_Syntax_Syntax.n in
                                  (match uu____9204 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9212) ->
                                       let uu____9229 =
                                         pat_vars env [] uv_args in
                                       (match uu____9229 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9243  ->
                                                      let uu____9244 =
                                                        let uu____9245 =
                                                          let uu____9246 =
                                                            let uu____9249 =
                                                              let uu____9250
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9250
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9249 in
                                                          fst uu____9246 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9245 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9244)) in
                                            let c1 =
                                              let uu____9256 =
                                                let uu____9257 =
                                                  let uu____9260 =
                                                    let uu____9261 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9261
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9260 in
                                                fst uu____9257 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9256 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9270 =
                                                let uu____9277 =
                                                  let uu____9283 =
                                                    let uu____9284 =
                                                      let uu____9287 =
                                                        let uu____9288 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9288
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9287 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9284 in
                                                  FStar_Util.Inl uu____9283 in
                                                Some uu____9277 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9270 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9308 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9313)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____9339 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____9339
                                 (fun _0_56  -> Some _0_56)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9358 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____9358 with
                                  | (args1,rest) ->
                                      let uu____9374 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____9374 with
                                       | (xs2,c2) ->
                                           let uu____9382 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____9382
                                             (fun uu____9393  ->
                                                match uu____9393 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9415 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____9415 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____9461 =
                                        let uu____9464 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9464 in
                                      FStar_All.pipe_right uu____9461
                                        (fun _0_57  -> Some _0_57))
                         | uu____9472 ->
                             let uu____9476 =
                               let uu____9477 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____9478 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____9479 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9477 uu____9478 uu____9479 in
                             failwith uu____9476 in
                       let uu____9483 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____9483
                         (fun uu____9511  ->
                            match uu____9511 with
                            | (xs1,c1) ->
                                let uu____9539 =
                                  let uu____9562 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9562) in
                                Some uu____9539)) in
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
                     let uu____9634 = imitate orig env wl1 st in
                     match uu____9634 with
                     | Failed uu____9639 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9645 = project orig env wl1 i st in
                      match uu____9645 with
                      | None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some (Failed uu____9652) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____9666 = FStar_Syntax_Util.head_and_args t21 in
                match uu____9666 with
                | (hd1,uu____9677) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9692 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9700 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9701 -> true
                     | uu____9716 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____9719 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____9719
                         then true
                         else
                           ((let uu____9722 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____9722
                             then
                               let uu____9723 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9723
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9731 =
                    let uu____9734 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____9734 FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____9731 FStar_Syntax_Free.names in
                let uu____9765 = FStar_Util.set_is_empty fvs_hd in
                if uu____9765
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____9774 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____9774 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9782 =
                            let uu____9783 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____9783 in
                          giveup_or_defer1 orig uu____9782
                        else
                          (let uu____9785 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____9785
                           then
                             let uu____9786 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____9786
                              then
                                let uu____9787 = subterms args_lhs in
                                imitate' orig env wl1 uu____9787
                              else
                                ((let uu____9791 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____9791
                                  then
                                    let uu____9792 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____9793 = names_to_string fvs1 in
                                    let uu____9794 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9792 uu____9793 uu____9794
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9799 ->
                                        let uu____9800 = sn_binders env vars in
                                        u_abs k_uv uu____9800 t21 in
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
                               (let uu____9809 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____9809
                                then
                                  ((let uu____9811 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____9811
                                    then
                                      let uu____9812 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____9813 = names_to_string fvs1 in
                                      let uu____9814 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9812 uu____9813 uu____9814
                                    else ());
                                   (let uu____9816 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9816
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
                     (let uu____9827 =
                        let uu____9828 = FStar_Syntax_Free.names t1 in
                        check_head uu____9828 t2 in
                      if uu____9827
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____9832 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____9832
                          then
                            let uu____9833 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9833
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9836 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9836 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9878 =
               match uu____9878 with
               | (t,u,k,args) ->
                   let uu____9908 = FStar_Syntax_Util.arrow_formals k in
                   (match uu____9908 with
                    | (all_formals,uu____9919) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____10011  ->
                                        match uu____10011 with
                                        | (x,imp) ->
                                            let uu____10018 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____10018, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____10026 = FStar_Syntax_Util.type_u () in
                                match uu____10026 with
                                | (t1,uu____10030) ->
                                    let uu____10031 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    fst uu____10031 in
                              let uu____10034 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____10034 with
                               | (t',tm_u1) ->
                                   let uu____10041 = destruct_flex_t t' in
                                   (match uu____10041 with
                                    | (uu____10063,u1,k1,uu____10066) ->
                                        let sol =
                                          let uu____10098 =
                                            let uu____10103 =
                                              u_abs k all_formals t' in
                                            ((u, k), uu____10103) in
                                          TERM uu____10098 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k1, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10167 = pat_var_opt env pat_args hd1 in
                              (match uu____10167 with
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
                                              (fun uu____10196  ->
                                                 match uu____10196 with
                                                 | (x,uu____10200) ->
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
                                      let uu____10206 =
                                        let uu____10207 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____10207 in
                                      if uu____10206
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10211 =
                                           FStar_Util.set_add (fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10211 formals1
                                           tl1)))
                          | uu____10217 -> failwith "Impossible" in
                        let uu____10228 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____10228 all_formals args) in
             let solve_both_pats wl1 uu____10268 uu____10269 r =
               match (uu____10268, uu____10269) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10383 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____10383
                   then
                     let uu____10384 = solve_prob orig None [] wl1 in
                     solve env uu____10384
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____10399 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____10399
                       then
                         let uu____10400 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____10401 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____10402 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____10403 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____10404 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10400 uu____10401 uu____10402 uu____10403
                           uu____10404
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____10446 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____10446 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10454 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____10454 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10484 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10484 in
                                  let uu____10487 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____10487 k3)
                           else
                             (let uu____10490 =
                                let uu____10491 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____10492 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____10493 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10491 uu____10492 uu____10493 in
                              failwith uu____10490) in
                       let uu____10494 =
                         let uu____10500 =
                           let uu____10508 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____10508 in
                         match uu____10500 with
                         | (bs,k1') ->
                             let uu____10526 =
                               let uu____10534 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____10534 in
                             (match uu____10526 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____10555 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_58  ->
                                         FStar_TypeChecker_Common.TProb _0_58)
                                      uu____10555 in
                                  let uu____10560 =
                                    let uu____10563 =
                                      let uu____10564 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____10564.FStar_Syntax_Syntax.n in
                                    let uu____10567 =
                                      let uu____10568 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____10568.FStar_Syntax_Syntax.n in
                                    (uu____10563, uu____10567) in
                                  (match uu____10560 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10576,uu____10577) ->
                                       (k1', [sub_prob])
                                   | (uu____10581,FStar_Syntax_Syntax.Tm_type
                                      uu____10582) -> (k2', [sub_prob])
                                   | uu____10586 ->
                                       let uu____10589 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____10589 with
                                        | (t,uu____10598) ->
                                            let uu____10599 = new_uvar r zs t in
                                            (match uu____10599 with
                                             | (k_zs,uu____10608) ->
                                                 let kprob =
                                                   let uu____10610 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_59  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_59) uu____10610 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____10494 with
                       | (k_u',sub_probs) ->
                           let uu____10624 =
                             let uu____10632 =
                               let uu____10633 = new_uvar r zs k_u' in
                               FStar_All.pipe_left FStar_Pervasives.fst
                                 uu____10633 in
                             let uu____10638 =
                               let uu____10641 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____10641 in
                             let uu____10644 =
                               let uu____10647 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____10647 in
                             (uu____10632, uu____10638, uu____10644) in
                           (match uu____10624 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____10666 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____10666 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____10678 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____10678
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____10682 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____10682 with
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
             let solve_one_pat uu____10714 uu____10715 =
               match (uu____10714, uu____10715) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10779 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____10779
                     then
                       let uu____10780 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10781 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10780 uu____10781
                     else ());
                    (let uu____10783 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____10783
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10790  ->
                              fun uu____10791  ->
                                match (uu____10790, uu____10791) with
                                | ((a,uu____10801),(t21,uu____10803)) ->
                                    let uu____10808 =
                                      let uu____10811 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____10811
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____10808
                                      (fun _0_60  ->
                                         FStar_TypeChecker_Common.TProb _0_60))
                           xs args2 in
                       let guard =
                         let uu____10815 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____10815 in
                       let wl1 = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____10825 = occurs_check env wl (u1, k1) t21 in
                        match uu____10825 with
                        | (occurs_ok,uu____10830) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____10835 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____10835
                            then
                              let sol =
                                let uu____10837 =
                                  let uu____10842 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____10842) in
                                TERM uu____10837 in
                              let wl1 = solve_prob orig None [sol] wl in
                              solve env wl1
                            else
                              (let uu____10847 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____10847
                               then
                                 let uu____10848 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____10848 with
                                 | (sol,(uu____10858,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____10868 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____10868
                                       then
                                         let uu____10869 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10869
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10874 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____10876 = lhs in
             match uu____10876 with
             | (t1,u1,k1,args1) ->
                 let uu____10881 = rhs in
                 (match uu____10881 with
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
                       | uu____10907 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____10913 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____10913 with
                              | (sol,uu____10920) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____10923 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____10923
                                    then
                                      let uu____10924 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____10924
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____10929 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____10931 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____10931
        then
          let uu____10932 = solve_prob orig None [] wl in
          solve env uu____10932
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____10936 = FStar_Util.physical_equality t1 t2 in
           if uu____10936
           then
             let uu____10937 = solve_prob orig None [] wl in
             solve env uu____10937
           else
             ((let uu____10940 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____10940
               then
                 let uu____10941 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____10941
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____10944,uu____10945) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____10946,FStar_Syntax_Syntax.Tm_bvar uu____10947) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___130_10987 =
                     match uu___130_10987 with
                     | [] -> c
                     | bs ->
                         let uu____11001 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c)) None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____11001 in
                   let uu____11011 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____11011 with
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
                                   let uu____11097 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____11097
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____11099 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.CProb _0_61)
                                   uu____11099))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___131_11176 =
                     match uu___131_11176 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l)) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____11211 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____11211 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11294 =
                                   let uu____11297 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____11298 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____11297
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11298 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_TypeChecker_Common.TProb _0_62)
                                   uu____11294))
               | (FStar_Syntax_Syntax.Tm_abs uu____11301,uu____11302) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11325 -> true
                     | uu____11340 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11368 =
                     let uu____11379 = maybe_eta t1 in
                     let uu____11384 = maybe_eta t2 in
                     (uu____11379, uu____11384) in
                   (match uu____11368 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___164_11415 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___164_11415.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___164_11415.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___164_11415.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___164_11415.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___164_11415.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___164_11415.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___164_11415.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___164_11415.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11434 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11434
                        then
                          let uu____11435 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11435 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11456 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11456
                        then
                          let uu____11457 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11457 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11462 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11473,FStar_Syntax_Syntax.Tm_abs uu____11474) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11497 -> true
                     | uu____11512 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11540 =
                     let uu____11551 = maybe_eta t1 in
                     let uu____11556 = maybe_eta t2 in
                     (uu____11551, uu____11556) in
                   (match uu____11540 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___164_11587 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___164_11587.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___164_11587.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___164_11587.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___164_11587.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___164_11587.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___164_11587.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___164_11587.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___164_11587.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11606 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11606
                        then
                          let uu____11607 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11607 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11628 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11628
                        then
                          let uu____11629 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11629 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11634 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11645,FStar_Syntax_Syntax.Tm_refine uu____11646) ->
                   let uu____11655 = as_refinement env wl t1 in
                   (match uu____11655 with
                    | (x1,phi1) ->
                        let uu____11660 = as_refinement env wl t2 in
                        (match uu____11660 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11666 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_63  ->
                                    FStar_TypeChecker_Common.TProb _0_63)
                                 uu____11666 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____11699 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____11699
                                 (guard_on_element wl problem x11) in
                             let fallback uu____11703 =
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
                                 let uu____11709 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____11709 impl in
                               let wl1 = solve_prob orig (Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11716 =
                                   let uu____11719 =
                                     let uu____11720 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____11720 :: (p_scope orig) in
                                   mk_problem uu____11719 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____11716 in
                               let uu____11723 =
                                 solve env1
                                   (let uu___165_11724 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___165_11724.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___165_11724.smt_ok);
                                      tcenv = (uu___165_11724.tcenv)
                                    }) in
                               (match uu____11723 with
                                | Failed uu____11728 -> fallback ()
                                | Success uu____11731 ->
                                    let guard =
                                      let uu____11735 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives.fst in
                                      let uu____11738 =
                                        let uu____11739 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives.fst in
                                        FStar_All.pipe_right uu____11739
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____11735
                                        uu____11738 in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl2 =
                                      let uu___166_11746 = wl1 in
                                      {
                                        attempting =
                                          (uu___166_11746.attempting);
                                        wl_deferred =
                                          (uu___166_11746.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___166_11746.defer_ok);
                                        smt_ok = (uu___166_11746.smt_ok);
                                        tcenv = (uu___166_11746.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11748,FStar_Syntax_Syntax.Tm_uvar uu____11749) ->
                   let uu____11770 = destruct_flex_t t1 in
                   let uu____11771 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11770 uu____11771
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11772;
                     FStar_Syntax_Syntax.tk = uu____11773;
                     FStar_Syntax_Syntax.pos = uu____11774;
                     FStar_Syntax_Syntax.vars = uu____11775;_},uu____11776),FStar_Syntax_Syntax.Tm_uvar
                  uu____11777) ->
                   let uu____11812 = destruct_flex_t t1 in
                   let uu____11813 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11812 uu____11813
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11814,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11815;
                     FStar_Syntax_Syntax.tk = uu____11816;
                     FStar_Syntax_Syntax.pos = uu____11817;
                     FStar_Syntax_Syntax.vars = uu____11818;_},uu____11819))
                   ->
                   let uu____11854 = destruct_flex_t t1 in
                   let uu____11855 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11854 uu____11855
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11856;
                     FStar_Syntax_Syntax.tk = uu____11857;
                     FStar_Syntax_Syntax.pos = uu____11858;
                     FStar_Syntax_Syntax.vars = uu____11859;_},uu____11860),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11861;
                     FStar_Syntax_Syntax.tk = uu____11862;
                     FStar_Syntax_Syntax.pos = uu____11863;
                     FStar_Syntax_Syntax.vars = uu____11864;_},uu____11865))
                   ->
                   let uu____11914 = destruct_flex_t t1 in
                   let uu____11915 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11914 uu____11915
               | (FStar_Syntax_Syntax.Tm_uvar uu____11916,uu____11917) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11928 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11928 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11932;
                     FStar_Syntax_Syntax.tk = uu____11933;
                     FStar_Syntax_Syntax.pos = uu____11934;
                     FStar_Syntax_Syntax.vars = uu____11935;_},uu____11936),uu____11937)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11962 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11962 t2 wl
               | (uu____11966,FStar_Syntax_Syntax.Tm_uvar uu____11967) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____11978,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11979;
                     FStar_Syntax_Syntax.tk = uu____11980;
                     FStar_Syntax_Syntax.pos = uu____11981;
                     FStar_Syntax_Syntax.vars = uu____11982;_},uu____11983))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12008,FStar_Syntax_Syntax.Tm_type uu____12009) ->
                   solve_t' env
                     (let uu___167_12020 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12020.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12020.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12020.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12020.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12020.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12020.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12020.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12020.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12020.FStar_TypeChecker_Common.rank)
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
                     (let uu___167_12051 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12051.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12051.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12051.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12051.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12051.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12051.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12051.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12051.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12051.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12052,FStar_Syntax_Syntax.Tm_arrow uu____12053) ->
                   solve_t' env
                     (let uu___167_12071 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12071.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12071.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12071.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12071.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12071.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12071.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12071.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12071.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12071.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12072;
                     FStar_Syntax_Syntax.tk = uu____12073;
                     FStar_Syntax_Syntax.pos = uu____12074;
                     FStar_Syntax_Syntax.vars = uu____12075;_},uu____12076),FStar_Syntax_Syntax.Tm_arrow
                  uu____12077) ->
                   solve_t' env
                     (let uu___167_12109 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12109.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12109.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12109.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12109.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12109.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12109.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12109.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12109.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12109.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____12110,uu____12111) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12124 =
                        let uu____12125 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12125 in
                      if uu____12124
                      then
                        let uu____12126 =
                          FStar_All.pipe_left
                            (fun _0_65  ->
                               FStar_TypeChecker_Common.TProb _0_65)
                            (let uu___168_12129 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_12129.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_12129.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_12129.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_12129.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_12129.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___168_12129.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_12129.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_12129.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_12129.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12130 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12126 uu____12130 t2
                          wl
                      else
                        (let uu____12135 = base_and_refinement env wl t2 in
                         match uu____12135 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12165 =
                                    FStar_All.pipe_left
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66)
                                      (let uu___169_12168 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___169_12168.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___169_12168.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___169_12168.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___169_12168.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___169_12168.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___169_12168.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___169_12168.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___169_12168.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___169_12168.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12169 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12165
                                    uu____12169 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___170_12184 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___170_12184.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___170_12184.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12187 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67)
                                      uu____12187 in
                                  let guard =
                                    let uu____12195 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12195
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12201;
                     FStar_Syntax_Syntax.tk = uu____12202;
                     FStar_Syntax_Syntax.pos = uu____12203;
                     FStar_Syntax_Syntax.vars = uu____12204;_},uu____12205),uu____12206)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12233 =
                        let uu____12234 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12234 in
                      if uu____12233
                      then
                        let uu____12235 =
                          FStar_All.pipe_left
                            (fun _0_68  ->
                               FStar_TypeChecker_Common.TProb _0_68)
                            (let uu___168_12238 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_12238.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_12238.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_12238.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_12238.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_12238.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___168_12238.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_12238.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_12238.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_12238.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12239 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12235 uu____12239 t2
                          wl
                      else
                        (let uu____12244 = base_and_refinement env wl t2 in
                         match uu____12244 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12274 =
                                    FStar_All.pipe_left
                                      (fun _0_69  ->
                                         FStar_TypeChecker_Common.TProb _0_69)
                                      (let uu___169_12277 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___169_12277.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___169_12277.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___169_12277.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___169_12277.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___169_12277.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___169_12277.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___169_12277.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___169_12277.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___169_12277.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12278 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12274
                                    uu____12278 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___170_12293 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___170_12293.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___170_12293.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12296 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_70  ->
                                         FStar_TypeChecker_Common.TProb _0_70)
                                      uu____12296 in
                                  let guard =
                                    let uu____12304 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12304
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12310,FStar_Syntax_Syntax.Tm_uvar uu____12311) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12323 = base_and_refinement env wl t1 in
                      match uu____12323 with
                      | (t_base,uu____12334) ->
                          solve_t env
                            (let uu___171_12349 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_12349.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_12349.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_12349.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_12349.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___171_12349.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_12349.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_12349.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_12349.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12352,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12353;
                     FStar_Syntax_Syntax.tk = uu____12354;
                     FStar_Syntax_Syntax.pos = uu____12355;
                     FStar_Syntax_Syntax.vars = uu____12356;_},uu____12357))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12383 = base_and_refinement env wl t1 in
                      match uu____12383 with
                      | (t_base,uu____12394) ->
                          solve_t env
                            (let uu___171_12409 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_12409.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_12409.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_12409.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_12409.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___171_12409.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_12409.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_12409.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_12409.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12412,uu____12413) ->
                   let t21 =
                     let uu____12421 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____12421 in
                   solve_t env
                     (let uu___172_12434 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___172_12434.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___172_12434.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___172_12434.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___172_12434.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___172_12434.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___172_12434.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___172_12434.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___172_12434.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___172_12434.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12435,FStar_Syntax_Syntax.Tm_refine uu____12436) ->
                   let t11 =
                     let uu____12444 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____12444 in
                   solve_t env
                     (let uu___173_12457 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_12457.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___173_12457.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___173_12457.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___173_12457.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_12457.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_12457.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_12457.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_12457.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_12457.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12460,uu____12461) ->
                   let head1 =
                     let uu____12480 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12480 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12511 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12511 FStar_Pervasives.fst in
                   let uu____12539 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12539
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12548 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12548
                      then
                        let guard =
                          let uu____12555 =
                            let uu____12556 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12556 = FStar_Syntax_Util.Equal in
                          if uu____12555
                          then None
                          else
                            (let uu____12559 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_71  -> Some _0_71)
                               uu____12559) in
                        let uu____12561 = solve_prob orig guard [] wl in
                        solve env uu____12561
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12564,uu____12565) ->
                   let head1 =
                     let uu____12573 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12573 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12604 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12604 FStar_Pervasives.fst in
                   let uu____12632 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12632
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12641 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12641
                      then
                        let guard =
                          let uu____12648 =
                            let uu____12649 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12649 = FStar_Syntax_Util.Equal in
                          if uu____12648
                          then None
                          else
                            (let uu____12652 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_72  -> Some _0_72)
                               uu____12652) in
                        let uu____12654 = solve_prob orig guard [] wl in
                        solve env uu____12654
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12657,uu____12658) ->
                   let head1 =
                     let uu____12662 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12662 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12693 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12693 FStar_Pervasives.fst in
                   let uu____12721 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12721
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12730 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12730
                      then
                        let guard =
                          let uu____12737 =
                            let uu____12738 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12738 = FStar_Syntax_Util.Equal in
                          if uu____12737
                          then None
                          else
                            (let uu____12741 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_73  -> Some _0_73)
                               uu____12741) in
                        let uu____12743 = solve_prob orig guard [] wl in
                        solve env uu____12743
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12746,uu____12747) ->
                   let head1 =
                     let uu____12751 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12751 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12782 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12782 FStar_Pervasives.fst in
                   let uu____12810 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12810
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12819 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12819
                      then
                        let guard =
                          let uu____12826 =
                            let uu____12827 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12827 = FStar_Syntax_Util.Equal in
                          if uu____12826
                          then None
                          else
                            (let uu____12830 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_74  -> Some _0_74)
                               uu____12830) in
                        let uu____12832 = solve_prob orig guard [] wl in
                        solve env uu____12832
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____12835,uu____12836) ->
                   let head1 =
                     let uu____12840 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12840 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12871 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12871 FStar_Pervasives.fst in
                   let uu____12899 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12899
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12908 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12908
                      then
                        let guard =
                          let uu____12915 =
                            let uu____12916 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12916 = FStar_Syntax_Util.Equal in
                          if uu____12915
                          then None
                          else
                            (let uu____12919 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_75  -> Some _0_75)
                               uu____12919) in
                        let uu____12921 = solve_prob orig guard [] wl in
                        solve env uu____12921
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____12924,uu____12925) ->
                   let head1 =
                     let uu____12938 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12938 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12969 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12969 FStar_Pervasives.fst in
                   let uu____12997 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12997
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13006 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13006
                      then
                        let guard =
                          let uu____13013 =
                            let uu____13014 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13014 = FStar_Syntax_Util.Equal in
                          if uu____13013
                          then None
                          else
                            (let uu____13017 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_76  -> Some _0_76)
                               uu____13017) in
                        let uu____13019 = solve_prob orig guard [] wl in
                        solve env uu____13019
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13022,FStar_Syntax_Syntax.Tm_match uu____13023) ->
                   let head1 =
                     let uu____13042 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13042 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13073 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13073 FStar_Pervasives.fst in
                   let uu____13101 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13101
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13110 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13110
                      then
                        let guard =
                          let uu____13117 =
                            let uu____13118 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13118 = FStar_Syntax_Util.Equal in
                          if uu____13117
                          then None
                          else
                            (let uu____13121 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_77  -> Some _0_77)
                               uu____13121) in
                        let uu____13123 = solve_prob orig guard [] wl in
                        solve env uu____13123
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13126,FStar_Syntax_Syntax.Tm_uinst uu____13127) ->
                   let head1 =
                     let uu____13135 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13135 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13166 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13166 FStar_Pervasives.fst in
                   let uu____13194 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13194
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13203 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13203
                      then
                        let guard =
                          let uu____13210 =
                            let uu____13211 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13211 = FStar_Syntax_Util.Equal in
                          if uu____13210
                          then None
                          else
                            (let uu____13214 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_78  -> Some _0_78)
                               uu____13214) in
                        let uu____13216 = solve_prob orig guard [] wl in
                        solve env uu____13216
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13219,FStar_Syntax_Syntax.Tm_name uu____13220) ->
                   let head1 =
                     let uu____13224 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13224 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13255 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13255 FStar_Pervasives.fst in
                   let uu____13283 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13283
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13292 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13292
                      then
                        let guard =
                          let uu____13299 =
                            let uu____13300 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13300 = FStar_Syntax_Util.Equal in
                          if uu____13299
                          then None
                          else
                            (let uu____13303 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_79  -> Some _0_79)
                               uu____13303) in
                        let uu____13305 = solve_prob orig guard [] wl in
                        solve env uu____13305
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13308,FStar_Syntax_Syntax.Tm_constant uu____13309) ->
                   let head1 =
                     let uu____13313 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13313 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13344 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13344 FStar_Pervasives.fst in
                   let uu____13372 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13372
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13381 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13381
                      then
                        let guard =
                          let uu____13388 =
                            let uu____13389 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13389 = FStar_Syntax_Util.Equal in
                          if uu____13388
                          then None
                          else
                            (let uu____13392 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_80  -> Some _0_80)
                               uu____13392) in
                        let uu____13394 = solve_prob orig guard [] wl in
                        solve env uu____13394
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13397,FStar_Syntax_Syntax.Tm_fvar uu____13398) ->
                   let head1 =
                     let uu____13402 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13402 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13433 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13433 FStar_Pervasives.fst in
                   let uu____13461 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13461
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13470 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13470
                      then
                        let guard =
                          let uu____13477 =
                            let uu____13478 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13478 = FStar_Syntax_Util.Equal in
                          if uu____13477
                          then None
                          else
                            (let uu____13481 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_81  -> Some _0_81)
                               uu____13481) in
                        let uu____13483 = solve_prob orig guard [] wl in
                        solve env uu____13483
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13486,FStar_Syntax_Syntax.Tm_app uu____13487) ->
                   let head1 =
                     let uu____13500 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13500 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13531 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13531 FStar_Pervasives.fst in
                   let uu____13559 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13559
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13568 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13568
                      then
                        let guard =
                          let uu____13575 =
                            let uu____13576 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13576 = FStar_Syntax_Util.Equal in
                          if uu____13575
                          then None
                          else
                            (let uu____13579 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_82  -> Some _0_82)
                               uu____13579) in
                        let uu____13581 = solve_prob orig guard [] wl in
                        solve env uu____13581
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13585,uu____13586),uu____13587) ->
                   solve_t' env
                     (let uu___174_13616 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_13616.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___174_13616.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___174_13616.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___174_13616.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_13616.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_13616.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_13616.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_13616.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_13616.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13619,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13621,uu____13622)) ->
                   solve_t' env
                     (let uu___175_13651 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_13651.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___175_13651.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___175_13651.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___175_13651.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_13651.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_13651.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_13651.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_13651.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_13651.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13652,uu____13653) ->
                   let uu____13661 =
                     let uu____13662 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13663 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13662
                       uu____13663 in
                   failwith uu____13661
               | (FStar_Syntax_Syntax.Tm_meta uu____13664,uu____13665) ->
                   let uu____13670 =
                     let uu____13671 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13672 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13671
                       uu____13672 in
                   failwith uu____13670
               | (FStar_Syntax_Syntax.Tm_delayed uu____13673,uu____13674) ->
                   let uu____13695 =
                     let uu____13696 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13697 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13696
                       uu____13697 in
                   failwith uu____13695
               | (uu____13698,FStar_Syntax_Syntax.Tm_meta uu____13699) ->
                   let uu____13704 =
                     let uu____13705 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13706 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13705
                       uu____13706 in
                   failwith uu____13704
               | (uu____13707,FStar_Syntax_Syntax.Tm_delayed uu____13708) ->
                   let uu____13729 =
                     let uu____13730 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13731 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13730
                       uu____13731 in
                   failwith uu____13729
               | (uu____13732,FStar_Syntax_Syntax.Tm_let uu____13733) ->
                   let uu____13741 =
                     let uu____13742 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13743 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13742
                       uu____13743 in
                   failwith uu____13741
               | uu____13744 -> giveup env "head tag mismatch" orig)))
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
          (let uu____13776 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____13776
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____13784  ->
                  fun uu____13785  ->
                    match (uu____13784, uu____13785) with
                    | ((a1,uu____13795),(a2,uu____13797)) ->
                        let uu____13802 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_83  -> FStar_TypeChecker_Common.TProb _0_83)
                          uu____13802)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____13808 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p) FStar_Pervasives.fst)
                 sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____13808 in
           let wl1 = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____13828 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____13835)::[] -> wp1
              | uu____13848 ->
                  let uu____13854 =
                    let uu____13855 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____13855 in
                  failwith uu____13854 in
            let uu____13858 =
              let uu____13864 =
                let uu____13865 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____13865 in
              [uu____13864] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____13858;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____13866 = lift_c1 () in solve_eq uu____13866 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___132_13870  ->
                       match uu___132_13870 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____13871 -> false)) in
             let uu____13872 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____13896)::uu____13897,(wp2,uu____13899)::uu____13900)
                   -> (wp1, wp2)
               | uu____13941 ->
                   let uu____13954 =
                     let uu____13955 =
                       let uu____13958 =
                         let uu____13959 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____13960 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____13959 uu____13960 in
                       (uu____13958, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____13955 in
                   raise uu____13954 in
             match uu____13872 with
             | (wpc1,wpc2) ->
                 let uu____13977 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____13977
                 then
                   let uu____13980 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env uu____13980 wl
                 else
                   (let uu____13984 =
                      let uu____13988 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____13988 in
                    match uu____13984 with
                    | (c2_decl,qualifiers) ->
                        let uu____14000 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____14000
                        then
                          let c1_repr =
                            let uu____14003 =
                              let uu____14004 =
                                let uu____14005 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____14005 in
                              let uu____14006 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14004 uu____14006 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14003 in
                          let c2_repr =
                            let uu____14008 =
                              let uu____14009 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____14010 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14009 uu____14010 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14008 in
                          let prob =
                            let uu____14012 =
                              let uu____14015 =
                                let uu____14016 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____14017 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____14016
                                  uu____14017 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____14015 in
                            FStar_TypeChecker_Common.TProb uu____14012 in
                          let wl1 =
                            let uu____14019 =
                              let uu____14021 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives.fst in
                              Some uu____14021 in
                            solve_prob orig uu____14019 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____14028 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____14028
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____14030 =
                                     let uu____14033 =
                                       let uu____14034 =
                                         let uu____14044 =
                                           let uu____14045 =
                                             let uu____14046 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____14046] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____14045 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____14047 =
                                           let uu____14049 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____14050 =
                                             let uu____14052 =
                                               let uu____14053 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____14053 in
                                             [uu____14052] in
                                           uu____14049 :: uu____14050 in
                                         (uu____14044, uu____14047) in
                                       FStar_Syntax_Syntax.Tm_app uu____14034 in
                                     FStar_Syntax_Syntax.mk uu____14033 in
                                   uu____14030
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____14064 =
                                    let uu____14067 =
                                      let uu____14068 =
                                        let uu____14078 =
                                          let uu____14079 =
                                            let uu____14080 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____14080] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____14079 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____14081 =
                                          let uu____14083 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____14084 =
                                            let uu____14086 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____14087 =
                                              let uu____14089 =
                                                let uu____14090 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14090 in
                                              [uu____14089] in
                                            uu____14086 :: uu____14087 in
                                          uu____14083 :: uu____14084 in
                                        (uu____14078, uu____14081) in
                                      FStar_Syntax_Syntax.Tm_app uu____14068 in
                                    FStar_Syntax_Syntax.mk uu____14067 in
                                  uu____14064
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____14101 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_TypeChecker_Common.TProb _0_84)
                               uu____14101 in
                           let wl1 =
                             let uu____14107 =
                               let uu____14109 =
                                 let uu____14112 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____14112 g in
                               FStar_All.pipe_left (fun _0_85  -> Some _0_85)
                                 uu____14109 in
                             solve_prob orig uu____14107 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____14122 = FStar_Util.physical_equality c1 c2 in
        if uu____14122
        then
          let uu____14123 = solve_prob orig None [] wl in
          solve env uu____14123
        else
          ((let uu____14126 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____14126
            then
              let uu____14127 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____14128 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14127
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14128
            else ());
           (let uu____14130 =
              let uu____14133 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____14134 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____14133, uu____14134) in
            match uu____14130 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14138),FStar_Syntax_Syntax.Total
                    (t2,uu____14140)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14153 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14153 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14156,FStar_Syntax_Syntax.Total uu____14157) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14169),FStar_Syntax_Syntax.Total
                    (t2,uu____14171)) ->
                     let uu____14184 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14184 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14188),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14190)) ->
                     let uu____14203 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14203 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14207),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14209)) ->
                     let uu____14222 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14222 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14225,FStar_Syntax_Syntax.Comp uu____14226) ->
                     let uu____14232 =
                       let uu___176_14235 = problem in
                       let uu____14238 =
                         let uu____14239 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14239 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_14235.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14238;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_14235.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_14235.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_14235.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_14235.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_14235.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_14235.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_14235.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_14235.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14232 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14240,FStar_Syntax_Syntax.Comp uu____14241) ->
                     let uu____14247 =
                       let uu___176_14250 = problem in
                       let uu____14253 =
                         let uu____14254 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14254 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_14250.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14253;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_14250.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_14250.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_14250.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_14250.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_14250.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_14250.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_14250.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_14250.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14247 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14255,FStar_Syntax_Syntax.GTotal uu____14256) ->
                     let uu____14262 =
                       let uu___177_14265 = problem in
                       let uu____14268 =
                         let uu____14269 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14269 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14265.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_14265.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14265.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14268;
                         FStar_TypeChecker_Common.element =
                           (uu___177_14265.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14265.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14265.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14265.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14265.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14265.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14262 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14270,FStar_Syntax_Syntax.Total uu____14271) ->
                     let uu____14277 =
                       let uu___177_14280 = problem in
                       let uu____14283 =
                         let uu____14284 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14284 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14280.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_14280.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14280.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14283;
                         FStar_TypeChecker_Common.element =
                           (uu___177_14280.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14280.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14280.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14280.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14280.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14280.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14277 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14285,FStar_Syntax_Syntax.Comp uu____14286) ->
                     let uu____14287 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____14287
                     then
                       let uu____14288 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type" in
                       solve_t env uu____14288 wl
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
                           (let uu____14298 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____14298
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14300 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____14300 with
                            | None  ->
                                let uu____14302 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14303 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____14303) in
                                if uu____14302
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
                                  (let uu____14306 =
                                     let uu____14307 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____14308 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14307 uu____14308 in
                                   giveup env uu____14306 orig)
                            | Some edge -> solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14313 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14329  ->
              match uu____14329 with
              | (uu____14336,uu____14337,u,uu____14339,uu____14340,uu____14341)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____14313 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14359 =
        FStar_All.pipe_right (fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____14359 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____14369 =
        FStar_All.pipe_right (snd ineqs)
          (FStar_List.map
             (fun uu____14381  ->
                match uu____14381 with
                | (u1,u2) ->
                    let uu____14386 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____14387 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____14386 uu____14387)) in
      FStar_All.pipe_right uu____14369 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14399,[])) -> "{}"
      | uu____14412 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14422 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____14422
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____14425 =
              FStar_List.map
                (fun uu____14429  ->
                   match uu____14429 with
                   | (uu____14432,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____14425 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____14436 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14436 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14474 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____14474
    then
      let uu____14475 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____14476 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14475
        (rel_to_string rel) uu____14476
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
            let uu____14496 =
              let uu____14498 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_86  -> Some _0_86) uu____14498 in
            FStar_Syntax_Syntax.new_bv uu____14496 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____14504 =
              let uu____14506 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_87  -> Some _0_87) uu____14506 in
            let uu____14508 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____14504 uu____14508 in
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
          let uu____14531 = FStar_Options.eager_inference () in
          if uu____14531
          then
            let uu___178_14532 = probs in
            {
              attempting = (uu___178_14532.attempting);
              wl_deferred = (uu___178_14532.wl_deferred);
              ctr = (uu___178_14532.ctr);
              defer_ok = false;
              smt_ok = (uu___178_14532.smt_ok);
              tcenv = (uu___178_14532.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Syntax_Unionfind.rollback tx;
             (let uu____14543 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____14543
              then
                let uu____14544 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____14544
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
          ((let uu____14554 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____14554
            then
              let uu____14555 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14555
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____14559 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____14559
             then
               let uu____14560 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14560
             else ());
            (let f2 =
               let uu____14563 =
                 let uu____14564 = FStar_Syntax_Util.unmeta f1 in
                 uu____14564.FStar_Syntax_Syntax.n in
               match uu____14563 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14568 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___179_14569 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___179_14569.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___179_14569.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___179_14569.FStar_TypeChecker_Env.implicits)
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
            let uu____14584 =
              let uu____14585 =
                let uu____14586 =
                  let uu____14587 =
                    FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____14587
                    (fun _0_88  -> FStar_TypeChecker_Common.NonTrivial _0_88) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14586;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____14585 in
            FStar_All.pipe_left (fun _0_89  -> Some _0_89) uu____14584
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____14620 =
        let uu____14621 =
          let uu____14622 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
          FStar_All.pipe_right uu____14622
            (fun _0_90  -> FStar_TypeChecker_Common.NonTrivial _0_90) in
        {
          FStar_TypeChecker_Env.guard_f = uu____14621;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      Some uu____14620
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
          (let uu____14648 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14648
           then
             let uu____14649 = FStar_Syntax_Print.term_to_string t1 in
             let uu____14650 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14649
               uu____14650
           else ());
          (let prob =
             let uu____14653 =
               let uu____14656 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____14656 in
             FStar_All.pipe_left
               (fun _0_91  -> FStar_TypeChecker_Common.TProb _0_91)
               uu____14653 in
           let g =
             let uu____14661 =
               let uu____14663 = singleton' env prob smt_ok in
               solve_and_commit env uu____14663 (fun uu____14664  -> None) in
             FStar_All.pipe_left (with_guard env prob) uu____14661 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14678 = try_teq true env t1 t2 in
        match uu____14678 with
        | None  ->
            let uu____14680 =
              let uu____14681 =
                let uu____14684 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                let uu____14685 = FStar_TypeChecker_Env.get_range env in
                (uu____14684, uu____14685) in
              FStar_Errors.Error uu____14681 in
            raise uu____14680
        | Some g ->
            ((let uu____14688 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____14688
              then
                let uu____14689 = FStar_Syntax_Print.term_to_string t1 in
                let uu____14690 = FStar_Syntax_Print.term_to_string t2 in
                let uu____14691 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14689
                  uu____14690 uu____14691
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
          (let uu____14707 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14707
           then
             let uu____14708 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____14709 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14708
               uu____14709
           else ());
          (let uu____14711 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____14711 with
           | (prob,x) ->
               let g =
                 let uu____14719 =
                   let uu____14721 = singleton' env prob smt_ok in
                   solve_and_commit env uu____14721
                     (fun uu____14722  -> None) in
                 FStar_All.pipe_left (with_guard env prob) uu____14719 in
               ((let uu____14728 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____14728
                 then
                   let uu____14729 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____14730 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____14731 =
                     let uu____14732 = FStar_Util.must g in
                     guard_to_string env uu____14732 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14729 uu____14730 uu____14731
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
          let uu____14756 = FStar_TypeChecker_Env.get_range env in
          let uu____14757 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.err uu____14756 uu____14757
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____14769 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____14769
         then
           let uu____14770 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____14771 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____14770
             uu____14771
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____14776 =
             let uu____14779 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None uu____14779 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_92  -> FStar_TypeChecker_Common.CProb _0_92) uu____14776 in
         let uu____14782 =
           let uu____14784 = singleton env prob in
           solve_and_commit env uu____14784 (fun uu____14785  -> None) in
         FStar_All.pipe_left (with_guard env prob) uu____14782)
let solve_universe_inequalities':
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____14804  ->
        match uu____14804 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____14829 =
                 let uu____14830 =
                   let uu____14833 =
                     let uu____14834 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____14835 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____14834 uu____14835 in
                   let uu____14836 = FStar_TypeChecker_Env.get_range env in
                   (uu____14833, uu____14836) in
                 FStar_Errors.Error uu____14830 in
               raise uu____14829) in
            let equiv1 v1 v' =
              let uu____14844 =
                let uu____14847 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____14848 = FStar_Syntax_Subst.compress_univ v' in
                (uu____14847, uu____14848) in
              match uu____14844 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____14859 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____14873 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____14873 with
                      | FStar_Syntax_Syntax.U_unif uu____14877 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____14890  ->
                                    match uu____14890 with
                                    | (u,v') ->
                                        let uu____14896 = equiv1 v1 v' in
                                        if uu____14896
                                        then
                                          let uu____14898 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____14898 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____14908 -> [])) in
            let uu____14911 =
              let wl =
                let uu___180_14914 = empty_worklist env in
                {
                  attempting = (uu___180_14914.attempting);
                  wl_deferred = (uu___180_14914.wl_deferred);
                  ctr = (uu___180_14914.ctr);
                  defer_ok = false;
                  smt_ok = (uu___180_14914.smt_ok);
                  tcenv = (uu___180_14914.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____14921  ->
                      match uu____14921 with
                      | (lb,v1) ->
                          let uu____14926 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____14926 with
                           | USolved wl1 -> ()
                           | uu____14928 -> fail lb v1))) in
            let rec check_ineq uu____14934 =
              match uu____14934 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____14941) -> true
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
                      uu____14956,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____14958,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____14965) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____14969,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____14974 -> false) in
            let uu____14977 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____14983  ->
                      match uu____14983 with
                      | (u,v1) ->
                          let uu____14988 = check_ineq (u, v1) in
                          if uu____14988
                          then true
                          else
                            ((let uu____14991 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____14991
                              then
                                let uu____14992 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____14993 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____14992
                                  uu____14993
                              else ());
                             false))) in
            if uu____14977
            then ()
            else
              ((let uu____14997 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____14997
                then
                  ((let uu____14999 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____14999);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____15005 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____15005))
                else ());
               (let uu____15011 =
                  let uu____15012 =
                    let uu____15015 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____15015) in
                  FStar_Errors.Error uu____15012 in
                raise uu____15011))
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
      let fail uu____15048 =
        match uu____15048 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____15058 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____15058
       then
         let uu____15059 = wl_to_string wl in
         let uu____15060 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____15059 uu____15060
       else ());
      (let g1 =
         let uu____15072 = solve_and_commit env wl fail in
         match uu____15072 with
         | Some [] ->
             let uu___181_15079 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___181_15079.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_15079.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_15079.FStar_TypeChecker_Env.implicits)
             }
         | uu____15082 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___182_15085 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___182_15085.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___182_15085.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___182_15085.FStar_TypeChecker_Env.implicits)
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
            let uu___183_15111 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___183_15111.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___183_15111.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___183_15111.FStar_TypeChecker_Env.implicits)
            } in
          let uu____15112 =
            let uu____15113 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____15113 in
          if uu____15112
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15119 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____15119
                   then
                     let uu____15120 = FStar_TypeChecker_Env.get_range env in
                     let uu____15121 =
                       let uu____15122 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15122 in
                     FStar_Errors.diag uu____15120 uu____15121
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
                         ((let uu____15131 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15131
                           then
                             let uu____15132 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____15133 =
                               let uu____15134 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15134 in
                             FStar_Errors.diag uu____15132 uu____15133
                           else ());
                          (let vcs =
                             let uu____15140 = FStar_Options.use_tactics () in
                             if uu____15140
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)] in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____15154  ->
                                   match uu____15154 with
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
      let uu____15165 = discharge_guard' None env g false in
      match uu____15165 with
      | Some g1 -> g1
      | None  ->
          let uu____15170 =
            let uu____15171 =
              let uu____15174 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____15174) in
            FStar_Errors.Error uu____15171 in
          raise uu____15170
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15181 = discharge_guard' None env g true in
      match uu____15181 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____15193 = FStar_Syntax_Unionfind.find u in
      match uu____15193 with | None  -> true | uu____15195 -> false in
    let rec until_fixpoint acc implicits =
      let uu____15208 = acc in
      match uu____15208 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____15254 = hd1 in
               (match uu____15254 with
                | (uu____15261,env,u,tm,k,r) ->
                    let uu____15267 = unresolved u in
                    if uu____15267
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm in
                       (let uu____15285 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck") in
                        if uu____15285
                        then
                          let uu____15286 =
                            FStar_Syntax_Print.uvar_to_string u in
                          let uu____15287 =
                            FStar_Syntax_Print.term_to_string tm1 in
                          let uu____15288 =
                            FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____15286 uu____15287 uu____15288
                        else ());
                       (let uu____15290 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___184_15294 = env1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___184_15294.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___184_15294.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___184_15294.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___184_15294.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___184_15294.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___184_15294.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___184_15294.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___184_15294.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___184_15294.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___184_15294.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___184_15294.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___184_15294.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___184_15294.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___184_15294.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___184_15294.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___184_15294.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___184_15294.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___184_15294.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___184_15294.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___184_15294.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___184_15294.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___184_15294.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___184_15294.FStar_TypeChecker_Env.qname_and_index)
                             }) tm1 in
                        match uu____15290 with
                        | (uu____15295,uu____15296,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___185_15299 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___185_15299.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___185_15299.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___185_15299.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____15302 =
                                discharge_guard'
                                  (Some
                                     (fun uu____15306  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____15302 with
                              | Some g3 -> g3
                              | None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
    let uu___186_15321 = g in
    let uu____15322 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___186_15321.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___186_15321.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___186_15321.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____15322
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____15350 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____15350 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15357 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15357
      | (reason,uu____15359,uu____15360,e,t,r)::uu____15364 ->
          let uu____15378 =
            let uu____15379 = FStar_Syntax_Print.term_to_string t in
            let uu____15380 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format3
              "Failed to resolve implicit argument of type '%s' introduced in %s because %s"
              uu____15379 uu____15380 reason in
          FStar_Errors.err r uu____15378
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___187_15387 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___187_15387.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___187_15387.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___187_15387.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15405 = try_teq false env t1 t2 in
        match uu____15405 with
        | None  -> false
        | Some g ->
            let uu____15408 = discharge_guard' None env g false in
            (match uu____15408 with
             | Some uu____15412 -> true
             | None  -> false)