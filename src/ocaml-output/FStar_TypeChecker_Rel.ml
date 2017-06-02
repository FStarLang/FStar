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
                      (fun _0_29  -> FStar_Util.Inl _0_29) in
                  Some uu____87 in
                FStar_Syntax_Util.abs uu____78 f uu____80 in
              FStar_All.pipe_left
                (fun _0_30  -> FStar_TypeChecker_Common.NonTrivial _0_30)
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
              (fun _0_31  -> FStar_TypeChecker_Common.NonTrivial _0_31)
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
            let uu___137_262 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___137_262.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___137_262.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___137_262.FStar_TypeChecker_Env.implicits)
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
            let uu___138_289 = g in
            let uu____290 =
              let uu____291 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____291 in
            {
              FStar_TypeChecker_Env.guard_f = uu____290;
              FStar_TypeChecker_Env.deferred =
                (uu___138_289.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___138_289.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___138_289.FStar_TypeChecker_Env.implicits)
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
  fun uu___106_568  ->
    match uu___106_568 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____581 =
    let uu____582 = FStar_Syntax_Subst.compress t in
    uu____582.FStar_Syntax_Syntax.n in
  match uu____581 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____599 = FStar_Syntax_Print.uvar_to_string u in
      let uu____600 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____599 uu____600
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____603;
         FStar_Syntax_Syntax.pos = uu____604;
         FStar_Syntax_Syntax.vars = uu____605;_},args)
      ->
      let uu____633 = FStar_Syntax_Print.uvar_to_string u in
      let uu____634 = FStar_Syntax_Print.term_to_string ty in
      let uu____635 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" uu____633 uu____634 uu____635
  | uu____636 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___107_642  ->
      match uu___107_642 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____646 =
            let uu____648 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____649 =
              let uu____651 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____652 =
                let uu____654 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____655 =
                  let uu____657 =
                    let uu____659 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____660 =
                      let uu____662 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____663 =
                        let uu____665 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (fst p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____666 =
                          let uu____668 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____668] in
                        uu____665 :: uu____666 in
                      uu____662 :: uu____663 in
                    uu____659 :: uu____660 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____657 in
                uu____654 :: uu____655 in
              uu____651 :: uu____652 in
            uu____648 :: uu____649 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____646
      | FStar_TypeChecker_Common.CProb p ->
          let uu____673 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____674 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____673
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____674
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___108_680  ->
      match uu___108_680 with
      | UNIV (u,t) ->
          let x =
            let uu____684 = FStar_Options.hide_uvar_nums () in
            if uu____684
            then "?"
            else
              (let uu____686 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____686 FStar_Util.string_of_int) in
          let uu____687 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____687
      | TERM ((u,uu____689),t) ->
          let x =
            let uu____694 = FStar_Options.hide_uvar_nums () in
            if uu____694
            then "?"
            else
              (let uu____696 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____696 FStar_Util.string_of_int) in
          let uu____697 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____697
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____706 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____706 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____714 =
      let uu____716 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____716
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____714 (FStar_String.concat ", ")
let args_to_string args =
  let uu____734 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____742  ->
            match uu____742 with
            | (x,uu____746) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right uu____734 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____751 =
      let uu____752 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____752 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____751;
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
        let uu___139_765 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___139_765.wl_deferred);
          ctr = (uu___139_765.ctr);
          defer_ok = (uu___139_765.defer_ok);
          smt_ok;
          tcenv = (uu___139_765.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___140_790 = empty_worklist env in
  let uu____791 = FStar_List.map FStar_Pervasives.snd g in
  {
    attempting = uu____791;
    wl_deferred = (uu___140_790.wl_deferred);
    ctr = (uu___140_790.ctr);
    defer_ok = false;
    smt_ok = (uu___140_790.smt_ok);
    tcenv = (uu___140_790.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___141_803 = wl in
        {
          attempting = (uu___141_803.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___141_803.ctr);
          defer_ok = (uu___141_803.defer_ok);
          smt_ok = (uu___141_803.smt_ok);
          tcenv = (uu___141_803.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___142_815 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___142_815.wl_deferred);
        ctr = (uu___142_815.ctr);
        defer_ok = (uu___142_815.defer_ok);
        smt_ok = (uu___142_815.smt_ok);
        tcenv = (uu___142_815.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____826 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____826
         then
           let uu____827 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____827
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___109_831  ->
    match uu___109_831 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___143_847 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___143_847.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___143_847.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___143_847.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___143_847.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___143_847.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___143_847.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___143_847.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___110_868  ->
    match uu___110_868 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_32  -> FStar_TypeChecker_Common.TProb _0_32)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_33  -> FStar_TypeChecker_Common.CProb _0_33)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___111_884  ->
      match uu___111_884 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___112_887  ->
    match uu___112_887 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___113_896  ->
    match uu___113_896 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___114_906  ->
    match uu___114_906 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___115_916  ->
    match uu___115_916 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun uu___116_927  ->
    match uu___116_927 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___117_938  ->
    match uu___117_938 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___118_947  ->
    match uu___118_947 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_34  -> FStar_TypeChecker_Common.TProb _0_34) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_35  -> FStar_TypeChecker_Common.CProb _0_35) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____961 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____961 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____972  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1022 = next_pid () in
  let uu____1023 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1022;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1023;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1070 = next_pid () in
  let uu____1071 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1070;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1071;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1112 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1112;
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
        let uu____1164 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1164
        then
          let uu____1165 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1166 = prob_to_string env d in
          let uu____1167 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1165 uu____1166 uu____1167 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1172 -> failwith "impossible" in
           let uu____1173 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1181 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1182 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1181, uu____1182)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1186 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1187 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1186, uu____1187) in
           match uu____1173 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___119_1196  ->
            match uu___119_1196 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1202 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1204),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___120_1217  ->
           match uu___120_1217 with
           | UNIV uu____1219 -> None
           | TERM ((u,uu____1223),t) ->
               let uu____1227 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1227 then Some t else None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___121_1239  ->
           match uu___121_1239 with
           | UNIV (u',t) ->
               let uu____1243 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1243 then Some t else None
           | uu____1246 -> None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1253 =
        let uu____1254 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1254 in
      FStar_Syntax_Subst.compress uu____1253
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1261 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1261
let norm_arg env t = let uu____1280 = sn env (fst t) in (uu____1280, (snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1297  ->
              match uu____1297 with
              | (x,imp) ->
                  let uu____1304 =
                    let uu___144_1305 = x in
                    let uu____1306 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___144_1305.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___144_1305.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1306
                    } in
                  (uu____1304, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1321 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1321
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1324 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1324
        | uu____1326 -> u2 in
      let uu____1327 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1327
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1434 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____1434 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1446;
               FStar_Syntax_Syntax.pos = uu____1447;
               FStar_Syntax_Syntax.vars = uu____1448;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1469 =
                 let uu____1470 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1471 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1470
                   uu____1471 in
               failwith uu____1469)
    | FStar_Syntax_Syntax.Tm_uinst uu____1481 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1508 =
             let uu____1509 = FStar_Syntax_Subst.compress t1' in
             uu____1509.FStar_Syntax_Syntax.n in
           match uu____1508 with
           | FStar_Syntax_Syntax.Tm_refine uu____1521 -> aux true t1'
           | uu____1526 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1538 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1561 =
             let uu____1562 = FStar_Syntax_Subst.compress t1' in
             uu____1562.FStar_Syntax_Syntax.n in
           match uu____1561 with
           | FStar_Syntax_Syntax.Tm_refine uu____1574 -> aux true t1'
           | uu____1579 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_app uu____1591 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1623 =
             let uu____1624 = FStar_Syntax_Subst.compress t1' in
             uu____1624.FStar_Syntax_Syntax.n in
           match uu____1623 with
           | FStar_Syntax_Syntax.Tm_refine uu____1636 -> aux true t1'
           | uu____1641 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_type uu____1653 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_constant uu____1665 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_name uu____1677 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1689 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1701 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_abs uu____1720 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1746 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_let uu____1766 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_match uu____1785 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_meta uu____1812 ->
        let uu____1817 =
          let uu____1818 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1819 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1818
            uu____1819 in
        failwith uu____1817
    | FStar_Syntax_Syntax.Tm_ascribed uu____1829 ->
        let uu____1847 =
          let uu____1848 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1849 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1848
            uu____1849 in
        failwith uu____1847
    | FStar_Syntax_Syntax.Tm_delayed uu____1859 ->
        let uu____1880 =
          let uu____1881 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1882 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1881
            uu____1882 in
        failwith uu____1880
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1892 =
          let uu____1893 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1894 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1893
            uu____1894 in
        failwith uu____1892 in
  let uu____1904 = whnf env t1 in aux false uu____1904
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1913 =
        let uu____1923 = empty_worklist env in
        base_and_refinement env uu____1923 t in
      FStar_All.pipe_right uu____1913 FStar_Pervasives.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____1947 = FStar_Syntax_Syntax.null_bv t in
    (uu____1947, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____1967 = base_and_refinement env wl t in
  match uu____1967 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
let force_refinement uu____2026 =
  match uu____2026 with
  | (t_base,refopt) ->
      let uu____2040 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base in
      (match uu____2040 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___122_2064  ->
      match uu___122_2064 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2068 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2069 =
            let uu____2070 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____2070 in
          let uu____2071 =
            let uu____2072 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____2072 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2068 uu____2069
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2071
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2076 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2077 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____2078 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2076 uu____2077
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2078
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2082 =
      let uu____2084 =
        let uu____2086 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2096  ->
                  match uu____2096 with | (uu____2100,uu____2101,x) -> x)) in
        FStar_List.append wl.attempting uu____2086 in
      FStar_List.map (wl_prob_to_string wl) uu____2084 in
    FStar_All.pipe_right uu____2082 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2119 =
          let uu____2129 =
            let uu____2130 = FStar_Syntax_Subst.compress k in
            uu____2130.FStar_Syntax_Syntax.n in
          match uu____2129 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2171 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2171)
              else
                (let uu____2185 = FStar_Syntax_Util.abs_formals t in
                 match uu____2185 with
                 | (ys',t1,uu____2206) ->
                     let uu____2219 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2219))
          | uu____2240 ->
              let uu____2241 =
                let uu____2247 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____2247) in
              ((ys, t), uu____2241) in
        match uu____2119 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2302 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2302 c in
               let uu____2304 =
                 let uu____2311 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_36  -> FStar_Util.Inl _0_36) in
                 FStar_All.pipe_right uu____2311 (fun _0_37  -> Some _0_37) in
               FStar_Syntax_Util.abs ys1 t1 uu____2304)
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
            let uu____2362 = p_guard prob in
            match uu____2362 with
            | (uu____2365,uv) ->
                ((let uu____2368 =
                    let uu____2369 = FStar_Syntax_Subst.compress uv in
                    uu____2369.FStar_Syntax_Syntax.n in
                  match uu____2368 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2389 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2389
                        then
                          let uu____2390 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2391 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2392 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2390
                            uu____2391 uu____2392
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2394 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___145_2397 = wl in
                  {
                    attempting = (uu___145_2397.attempting);
                    wl_deferred = (uu___145_2397.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___145_2397.defer_ok);
                    smt_ok = (uu___145_2397.smt_ok);
                    tcenv = (uu___145_2397.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2410 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2410
         then
           let uu____2411 = FStar_Util.string_of_int pid in
           let uu____2412 =
             let uu____2413 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2413 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2411 uu____2412
         else ());
        commit sol;
        (let uu___146_2418 = wl in
         {
           attempting = (uu___146_2418.attempting);
           wl_deferred = (uu___146_2418.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___146_2418.defer_ok);
           smt_ok = (uu___146_2418.smt_ok);
           tcenv = (uu___146_2418.tcenv)
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
            | (uu____2447,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2455 = FStar_Syntax_Util.mk_conj t1 f in
                Some uu____2455 in
          (let uu____2461 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2461
           then
             let uu____2462 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2463 =
               let uu____2464 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2464 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2462 uu____2463
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2489 =
    let uu____2493 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2493 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2489
    (FStar_Util.for_some
       (fun uu____2510  ->
          match uu____2510 with
          | (uv,uu____2514) -> FStar_Syntax_Unionfind.equiv uv (fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2547 = occurs wl uk t in Prims.op_Negation uu____2547 in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2552 =
         let uu____2553 = FStar_Syntax_Print.uvar_to_string (fst uk) in
         let uu____2554 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2553 uu____2554 in
       Some uu____2552) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2602 = occurs_check env wl uk t in
  match uu____2602 with
  | (occurs_ok,msg) ->
      let uu____2619 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2619, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2683 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2707  ->
            fun uu____2708  ->
              match (uu____2707, uu____2708) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2751 =
                    let uu____2752 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2752 in
                  if uu____2751
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2766 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2766
                     then
                       let uu____2773 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____2773)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2683 with | (isect,uu____2795) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2844  ->
          fun uu____2845  ->
            match (uu____2844, uu____2845) with
            | ((a,uu____2855),(b,uu____2857)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2901 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2907  ->
                match uu____2907 with
                | (b,uu____2911) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____2901 then None else Some (a, (snd hd1))
  | uu____2920 -> None
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
            let uu____2963 = pat_var_opt env seen hd1 in
            (match uu____2963 with
             | None  ->
                 ((let uu____2971 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____2971
                   then
                     let uu____2972 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____2972
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2984 =
      let uu____2985 = FStar_Syntax_Subst.compress t in
      uu____2985.FStar_Syntax_Syntax.n in
    match uu____2984 with
    | FStar_Syntax_Syntax.Tm_uvar uu____2988 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____2997;
           FStar_Syntax_Syntax.tk = uu____2998;
           FStar_Syntax_Syntax.pos = uu____2999;
           FStar_Syntax_Syntax.vars = uu____3000;_},uu____3001)
        -> true
    | uu____3024 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3086;
         FStar_Syntax_Syntax.pos = uu____3087;
         FStar_Syntax_Syntax.vars = uu____3088;_},args)
      -> (t, uv, k, args)
  | uu____3129 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____3183 = destruct_flex_t t in
  match uu____3183 with
  | (t1,uv,k,args) ->
      let uu____3251 = pat_vars env [] args in
      (match uu____3251 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3307 -> ((t1, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth option*
  FStar_Syntax_Syntax.delta_depth option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3355 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth option* FStar_Syntax_Syntax.delta_depth
      option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3378 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3382 -> false
let head_match: match_result -> match_result =
  fun uu___123_3385  ->
    match uu___123_3385 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3394 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3407 ->
          let uu____3408 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3408 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3418 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3432 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3438 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> None
      | FStar_Syntax_Syntax.Tm_bvar uu____3460 -> None
      | FStar_Syntax_Syntax.Tm_name uu____3461 -> None
      | FStar_Syntax_Syntax.Tm_uvar uu____3462 -> None
      | FStar_Syntax_Syntax.Tm_let uu____3471 -> None
      | FStar_Syntax_Syntax.Tm_match uu____3479 -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3496) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3502,uu____3503) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3533) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3548;
             FStar_Syntax_Syntax.index = uu____3549;
             FStar_Syntax_Syntax.sort = t2;_},uu____3551)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3558 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3559 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3560 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3568 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3584 = fv_delta_depth env fv in Some uu____3584
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
            let uu____3603 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3603
            then FullMatch
            else
              (let uu____3605 =
                 let uu____3610 =
                   let uu____3612 = fv_delta_depth env f in Some uu____3612 in
                 let uu____3613 =
                   let uu____3615 = fv_delta_depth env g in Some uu____3615 in
                 (uu____3610, uu____3613) in
               MisMatch uu____3605)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3619),FStar_Syntax_Syntax.Tm_uinst (g,uu____3621)) ->
            let uu____3630 = head_matches env f g in
            FStar_All.pipe_right uu____3630 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3637),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3639)) ->
            let uu____3664 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____3664 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3669),FStar_Syntax_Syntax.Tm_refine (y,uu____3671)) ->
            let uu____3680 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3680 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3682),uu____3683) ->
            let uu____3688 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3688 head_match
        | (uu____3689,FStar_Syntax_Syntax.Tm_refine (x,uu____3691)) ->
            let uu____3696 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3696 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3697,FStar_Syntax_Syntax.Tm_type
           uu____3698) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3699,FStar_Syntax_Syntax.Tm_arrow uu____3700) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3716),FStar_Syntax_Syntax.Tm_app (head',uu____3718))
            ->
            let uu____3747 = head_matches env head1 head' in
            FStar_All.pipe_right uu____3747 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3749),uu____3750) ->
            let uu____3765 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____3765 head_match
        | (uu____3766,FStar_Syntax_Syntax.Tm_app (head1,uu____3768)) ->
            let uu____3783 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____3783 head_match
        | uu____3784 ->
            let uu____3787 =
              let uu____3792 = delta_depth_of_term env t11 in
              let uu____3794 = delta_depth_of_term env t21 in
              (uu____3792, uu____3794) in
            MisMatch uu____3787
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3830 = FStar_Syntax_Util.head_and_args t in
    match uu____3830 with
    | (head1,uu____3842) ->
        let uu____3857 =
          let uu____3858 = FStar_Syntax_Util.un_uinst head1 in
          uu____3858.FStar_Syntax_Syntax.n in
        (match uu____3857 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3863 =
               let uu____3864 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____3864 FStar_Option.isSome in
             if uu____3863
             then
               let uu____3878 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____3878 (fun _0_38  -> Some _0_38)
             else None
         | uu____3881 -> None) in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None)) in
  let fail r = (r, None) in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21 in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),uu____3949) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____3959 =
             let uu____3964 = maybe_inline t11 in
             let uu____3966 = maybe_inline t21 in (uu____3964, uu____3966) in
           match uu____3959 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (uu____3987,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____3997 =
             let uu____4002 = maybe_inline t11 in
             let uu____4004 = maybe_inline t21 in (uu____4002, uu____4004) in
           match uu____3997 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____4029 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____4029 with
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
        let uu____4044 =
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
             let uu____4052 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____4052)) in
        (match uu____4044 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4060 -> fail r
    | uu____4065 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4090 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4120 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4135 = FStar_Syntax_Util.type_u () in
      match uu____4135 with
      | (t,uu____4139) ->
          let uu____4140 = new_uvar r binders t in fst uu____4140
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4149 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____4149 FStar_Pervasives.fst
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
        let uu____4191 = head_matches env t1 t' in
        match uu____4191 with
        | MisMatch uu____4192 -> false
        | uu____4197 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4257,imp),T (t2,uu____4260)) -> (t2, imp)
                     | uu____4277 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4317  ->
                    match uu____4317 with
                    | (t2,uu____4325) ->
                        (None, INVARIANT, (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let fail uu____4358 = failwith "Bad reconstruction" in
          let uu____4359 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____4359 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4412))::tcs2) ->
                       aux
                         (((let uu___147_4434 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___147_4434.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___147_4434.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4444 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___124_4475 =
                 match uu___124_4475 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4538 = decompose1 [] bs1 in
               (rebuild, matches, uu____4538))
      | uu____4566 ->
          let rebuild uu___125_4571 =
            match uu___125_4571 with
            | [] -> t1
            | uu____4573 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___126_4592  ->
    match uu___126_4592 with
    | T (t,uu____4594) -> t
    | uu____4603 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___127_4606  ->
    match uu___127_4606 with
    | T (t,uu____4608) -> FStar_Syntax_Syntax.as_arg t
    | uu____4617 -> failwith "Impossible"
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
              | (uu____4686,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4705 = new_uvar r scope1 k in
                  (match uu____4705 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4717 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args)) None r in
                       let uu____4732 =
                         let uu____4733 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_39  ->
                              FStar_TypeChecker_Common.TProb _0_39)
                           uu____4733 in
                       ((T (gi_xs, mk_kind)), uu____4732))
              | (uu____4742,uu____4743,C uu____4744) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4831 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4842;
                         FStar_Syntax_Syntax.pos = uu____4843;
                         FStar_Syntax_Syntax.vars = uu____4844;_})
                        ->
                        let uu____4859 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4859 with
                         | (T (gi_xs,uu____4875),prob) ->
                             let uu____4885 =
                               let uu____4886 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_40  -> C _0_40)
                                 uu____4886 in
                             (uu____4885, [prob])
                         | uu____4888 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4898;
                         FStar_Syntax_Syntax.pos = uu____4899;
                         FStar_Syntax_Syntax.vars = uu____4900;_})
                        ->
                        let uu____4915 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4915 with
                         | (T (gi_xs,uu____4931),prob) ->
                             let uu____4941 =
                               let uu____4942 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_41  -> C _0_41)
                                 uu____4942 in
                             (uu____4941, [prob])
                         | uu____4944 -> failwith "impossible")
                    | (uu____4950,uu____4951,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____4953;
                         FStar_Syntax_Syntax.pos = uu____4954;
                         FStar_Syntax_Syntax.vars = uu____4955;_})
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
                        let uu____5029 =
                          let uu____5034 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____5034 FStar_List.unzip in
                        (match uu____5029 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5063 =
                                 let uu____5064 =
                                   let uu____5067 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____5067 un_T in
                                 let uu____5068 =
                                   let uu____5074 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____5074
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5064;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5068;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5063 in
                             ((C gi_xs), sub_probs))
                    | uu____5079 ->
                        let uu____5086 = sub_prob scope1 args q in
                        (match uu____5086 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____4831 with
                   | (tc,probs) ->
                       let uu____5104 =
                         match q with
                         | (Some b,uu____5130,uu____5131) ->
                             let uu____5139 =
                               let uu____5143 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____5143 :: args in
                             ((Some b), (b :: scope1), uu____5139)
                         | uu____5161 -> (None, scope1, args) in
                       (match uu____5104 with
                        | (bopt,scope2,args1) ->
                            let uu____5204 = aux scope2 args1 qs2 in
                            (match uu____5204 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____5225 =
                                         let uu____5227 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         f :: uu____5227 in
                                       FStar_Syntax_Util.mk_conj_l uu____5225
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (fst b).FStar_Syntax_Syntax.sort in
                                       let uu____5240 =
                                         let uu____5242 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (fst b) f in
                                         let uu____5243 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         uu____5242 :: uu____5243 in
                                       FStar_Syntax_Util.mk_conj_l uu____5240 in
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
  let uu___148_5296 = p in
  let uu____5299 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____5300 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___148_5296.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5299;
    FStar_TypeChecker_Common.relation =
      (uu___148_5296.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5300;
    FStar_TypeChecker_Common.element =
      (uu___148_5296.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___148_5296.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___148_5296.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___148_5296.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___148_5296.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___148_5296.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5310 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____5310
            (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
      | FStar_TypeChecker_Common.CProb uu____5315 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5329 = compress_prob wl pr in
        FStar_All.pipe_right uu____5329 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5335 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____5335 with
           | (lh,uu____5348) ->
               let uu____5363 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____5363 with
                | (rh,uu____5376) ->
                    let uu____5391 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5400,FStar_Syntax_Syntax.Tm_uvar uu____5401)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5420,uu____5421)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5432,FStar_Syntax_Syntax.Tm_uvar uu____5433)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5444,uu____5445)
                          ->
                          let uu____5454 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5454 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5494 ->
                                    let rank =
                                      let uu____5501 = is_top_level_prob prob in
                                      if uu____5501
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5503 =
                                      let uu___149_5506 = tp in
                                      let uu____5509 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_5506.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___149_5506.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_5506.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5509;
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_5506.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_5506.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_5506.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_5506.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_5506.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_5506.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5503)))
                      | (uu____5519,FStar_Syntax_Syntax.Tm_uvar uu____5520)
                          ->
                          let uu____5529 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5529 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5569 ->
                                    let uu____5575 =
                                      let uu___150_5580 = tp in
                                      let uu____5583 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___150_5580.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5583;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___150_5580.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___150_5580.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___150_5580.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___150_5580.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___150_5580.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___150_5580.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___150_5580.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___150_5580.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5575)))
                      | (uu____5599,uu____5600) -> (rigid_rigid, tp) in
                    (match uu____5391 with
                     | (rank,tp1) ->
                         let uu____5611 =
                           FStar_All.pipe_right
                             (let uu___151_5614 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___151_5614.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___151_5614.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___151_5614.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___151_5614.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___151_5614.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___151_5614.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___151_5614.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___151_5614.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___151_5614.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_43  ->
                                FStar_TypeChecker_Common.TProb _0_43) in
                         (rank, uu____5611))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5620 =
            FStar_All.pipe_right
              (let uu___152_5623 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___152_5623.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___152_5623.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___152_5623.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___152_5623.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___152_5623.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___152_5623.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___152_5623.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___152_5623.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___152_5623.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) in
          (rigid_rigid, uu____5620)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob option* FStar_TypeChecker_Common.prob
      Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____5655 probs =
      match uu____5655 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5685 = rank wl hd1 in
               (match uu____5685 with
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
    match projectee with | UDeferred _0 -> true | uu____5750 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5762 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5774 -> false
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
                        let uu____5807 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____5807 with
                        | (k,uu____5811) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____5815 -> false)))
            | uu____5816 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____5859 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____5859 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5862 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____5868 =
                     let uu____5869 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____5870 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5869
                       uu____5870 in
                   UFailed uu____5868)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5886 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5886 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5904 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5904 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____5907 ->
                let uu____5910 =
                  let uu____5911 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____5912 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5911
                    uu____5912 msg in
                UFailed uu____5910 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____5913,uu____5914) ->
              let uu____5915 =
                let uu____5916 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5917 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5916 uu____5917 in
              failwith uu____5915
          | (FStar_Syntax_Syntax.U_unknown ,uu____5918) ->
              let uu____5919 =
                let uu____5920 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5921 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5920 uu____5921 in
              failwith uu____5919
          | (uu____5922,FStar_Syntax_Syntax.U_bvar uu____5923) ->
              let uu____5924 =
                let uu____5925 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5926 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5925 uu____5926 in
              failwith uu____5924
          | (uu____5927,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____5928 =
                let uu____5929 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5930 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5929 uu____5930 in
              failwith uu____5928
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____5942 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____5942
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____5952 = occurs_univ v1 u3 in
              if uu____5952
              then
                let uu____5953 =
                  let uu____5954 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____5955 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5954 uu____5955 in
                try_umax_components u11 u21 uu____5953
              else
                (let uu____5957 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____5957)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____5965 = occurs_univ v1 u3 in
              if uu____5965
              then
                let uu____5966 =
                  let uu____5967 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____5968 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5967 uu____5968 in
                try_umax_components u11 u21 uu____5966
              else
                (let uu____5970 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____5970)
          | (FStar_Syntax_Syntax.U_max uu____5973,uu____5974) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____5979 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____5979
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____5981,FStar_Syntax_Syntax.U_max uu____5982) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____5987 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____5987
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____5989,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____5990,FStar_Syntax_Syntax.U_name
             uu____5991) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____5992) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____5993) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____5994,FStar_Syntax_Syntax.U_succ
             uu____5995) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____5996,FStar_Syntax_Syntax.U_zero
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
  let uu____6058 = bc1 in
  match uu____6058 with
  | (bs1,mk_cod1) ->
      let uu____6083 = bc2 in
      (match uu____6083 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6130 = FStar_Util.first_N n1 bs in
             match uu____6130 with
             | (bs3,rest) ->
                 let uu____6144 = mk_cod rest in (bs3, uu____6144) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____6162 =
               let uu____6166 = mk_cod1 [] in (bs1, uu____6166) in
             let uu____6168 =
               let uu____6172 = mk_cod2 [] in (bs2, uu____6172) in
             (uu____6162, uu____6168)
           else
             if l1 > l2
             then
               (let uu____6194 = curry l2 bs1 mk_cod1 in
                let uu____6201 =
                  let uu____6205 = mk_cod2 [] in (bs2, uu____6205) in
                (uu____6194, uu____6201))
             else
               (let uu____6214 =
                  let uu____6218 = mk_cod1 [] in (bs1, uu____6218) in
                let uu____6220 = curry l1 bs2 mk_cod2 in
                (uu____6214, uu____6220)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6324 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____6324
       then
         let uu____6325 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6325
       else ());
      (let uu____6327 = next_prob probs in
       match uu____6327 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___153_6340 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___153_6340.wl_deferred);
               ctr = (uu___153_6340.ctr);
               defer_ok = (uu___153_6340.defer_ok);
               smt_ok = (uu___153_6340.smt_ok);
               tcenv = (uu___153_6340.tcenv)
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
                  let uu____6347 = solve_flex_rigid_join env tp probs1 in
                  (match uu____6347 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6351 = solve_rigid_flex_meet env tp probs1 in
                     match uu____6351 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____6355,uu____6356) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6365 ->
                let uu____6370 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6398  ->
                          match uu____6398 with
                          | (c,uu____6403,uu____6404) -> c < probs.ctr)) in
                (match uu____6370 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6426 =
                            FStar_List.map
                              (fun uu____6432  ->
                                 match uu____6432 with
                                 | (uu____6438,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____6426
                      | uu____6441 ->
                          let uu____6446 =
                            let uu___154_6447 = probs in
                            let uu____6448 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6457  ->
                                      match uu____6457 with
                                      | (uu____6461,uu____6462,y) -> y)) in
                            {
                              attempting = uu____6448;
                              wl_deferred = rest;
                              ctr = (uu___154_6447.ctr);
                              defer_ok = (uu___154_6447.defer_ok);
                              smt_ok = (uu___154_6447.smt_ok);
                              tcenv = (uu___154_6447.tcenv)
                            } in
                          solve env uu____6446))))
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
            let uu____6469 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____6469 with
            | USolved wl1 ->
                let uu____6471 = solve_prob orig None [] wl1 in
                solve env uu____6471
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
                  let uu____6505 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6505 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6508 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6516;
                  FStar_Syntax_Syntax.pos = uu____6517;
                  FStar_Syntax_Syntax.vars = uu____6518;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6521;
                  FStar_Syntax_Syntax.pos = uu____6522;
                  FStar_Syntax_Syntax.vars = uu____6523;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6535,uu____6536) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6541,FStar_Syntax_Syntax.Tm_uinst uu____6542) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6547 -> USolved wl
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
            ((let uu____6555 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6555
              then
                let uu____6556 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6556 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6564 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6564
         then
           let uu____6565 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6565
         else ());
        (let uu____6567 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6567 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6609 = head_matches_delta env () t1 t2 in
               match uu____6609 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6631 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6657 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6666 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____6667 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____6666, uu____6667)
                          | None  ->
                              let uu____6670 = FStar_Syntax_Subst.compress t1 in
                              let uu____6671 = FStar_Syntax_Subst.compress t2 in
                              (uu____6670, uu____6671) in
                        (match uu____6657 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6693 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_45  ->
                                    FStar_TypeChecker_Common.TProb _0_45)
                                 uu____6693 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6716 =
                                    let uu____6722 =
                                      let uu____6725 =
                                        let uu____6728 =
                                          let uu____6729 =
                                            let uu____6734 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____6734) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6729 in
                                        FStar_Syntax_Syntax.mk uu____6728 in
                                      uu____6725 None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____6747 =
                                      let uu____6749 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____6749] in
                                    (uu____6722, uu____6747) in
                                  Some uu____6716
                              | (uu____6758,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6760)) ->
                                  let uu____6765 =
                                    let uu____6769 =
                                      let uu____6771 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____6771] in
                                    (t11, uu____6769) in
                                  Some uu____6765
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6777),uu____6778) ->
                                  let uu____6783 =
                                    let uu____6787 =
                                      let uu____6789 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____6789] in
                                    (t21, uu____6787) in
                                  Some uu____6783
                              | uu____6794 ->
                                  let uu____6797 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____6797 with
                                   | (head1,uu____6812) ->
                                       let uu____6827 =
                                         let uu____6828 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____6828.FStar_Syntax_Syntax.n in
                                       (match uu____6827 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6835;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6837;_}
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
                                        | uu____6846 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6855) ->
                  let uu____6868 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___128_6877  ->
                            match uu___128_6877 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6882 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____6882 with
                                      | (u',uu____6893) ->
                                          let uu____6908 =
                                            let uu____6909 = whnf env u' in
                                            uu____6909.FStar_Syntax_Syntax.n in
                                          (match uu____6908 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____6913) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____6926 -> false))
                                 | uu____6927 -> false)
                            | uu____6929 -> false)) in
                  (match uu____6868 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____6950 tps =
                         match uu____6950 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____6977 =
                                    let uu____6982 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____6982 in
                                  (match uu____6977 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____7001 -> None) in
                       let uu____7006 =
                         let uu____7011 =
                           let uu____7015 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____7015, []) in
                         make_lower_bound uu____7011 lower_bounds in
                       (match uu____7006 with
                        | None  ->
                            ((let uu____7022 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7022
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
                            ((let uu____7035 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7035
                              then
                                let wl' =
                                  let uu___155_7037 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___155_7037.wl_deferred);
                                    ctr = (uu___155_7037.ctr);
                                    defer_ok = (uu___155_7037.defer_ok);
                                    smt_ok = (uu___155_7037.smt_ok);
                                    tcenv = (uu___155_7037.tcenv)
                                  } in
                                let uu____7038 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7038
                              else ());
                             (let uu____7040 =
                                solve_t env eq_prob
                                  (let uu___156_7041 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___156_7041.wl_deferred);
                                     ctr = (uu___156_7041.ctr);
                                     defer_ok = (uu___156_7041.defer_ok);
                                     smt_ok = (uu___156_7041.smt_ok);
                                     tcenv = (uu___156_7041.tcenv)
                                   }) in
                              match uu____7040 with
                              | Success uu____7043 ->
                                  let wl1 =
                                    let uu___157_7045 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___157_7045.wl_deferred);
                                      ctr = (uu___157_7045.ctr);
                                      defer_ok = (uu___157_7045.defer_ok);
                                      smt_ok = (uu___157_7045.smt_ok);
                                      tcenv = (uu___157_7045.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1 in
                                  let uu____7047 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds in
                                  Some wl2
                              | uu____7050 -> None))))
              | uu____7051 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7058 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____7058
         then
           let uu____7059 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7059
         else ());
        (let uu____7061 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____7061 with
         | (u,args) ->
             let uu____7088 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____7088 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____7119 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____7119 with
                    | (h1,args1) ->
                        let uu____7147 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____7147 with
                         | (h2,uu____7160) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7179 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____7179
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7192 =
                                          let uu____7194 =
                                            let uu____7195 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_46  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_46) uu____7195 in
                                          [uu____7194] in
                                        Some uu____7192))
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
                                       (let uu____7217 =
                                          let uu____7219 =
                                            let uu____7220 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_47  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_47) uu____7220 in
                                          [uu____7219] in
                                        Some uu____7217))
                                  else None
                              | uu____7228 -> None)) in
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
                             let uu____7294 =
                               let uu____7300 =
                                 let uu____7303 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____7303 in
                               (uu____7300, m1) in
                             Some uu____7294)
                    | (uu____7312,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7314)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7346),uu____7347) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____7378 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7412) ->
                       let uu____7425 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___129_7434  ->
                                 match uu___129_7434 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____7439 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____7439 with
                                           | (u',uu____7450) ->
                                               let uu____7465 =
                                                 let uu____7466 = whnf env u' in
                                                 uu____7466.FStar_Syntax_Syntax.n in
                                               (match uu____7465 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7470) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____7483 -> false))
                                      | uu____7484 -> false)
                                 | uu____7486 -> false)) in
                       (match uu____7425 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7511 tps =
                              match uu____7511 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7552 =
                                         let uu____7559 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7559 in
                                       (match uu____7552 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7594 -> None) in
                            let uu____7601 =
                              let uu____7608 =
                                let uu____7614 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7614, []) in
                              make_upper_bound uu____7608 upper_bounds in
                            (match uu____7601 with
                             | None  ->
                                 ((let uu____7623 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7623
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
                                 ((let uu____7642 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7642
                                   then
                                     let wl' =
                                       let uu___158_7644 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___158_7644.wl_deferred);
                                         ctr = (uu___158_7644.ctr);
                                         defer_ok = (uu___158_7644.defer_ok);
                                         smt_ok = (uu___158_7644.smt_ok);
                                         tcenv = (uu___158_7644.tcenv)
                                       } in
                                     let uu____7645 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7645
                                   else ());
                                  (let uu____7647 =
                                     solve_t env eq_prob
                                       (let uu___159_7648 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___159_7648.wl_deferred);
                                          ctr = (uu___159_7648.ctr);
                                          defer_ok = (uu___159_7648.defer_ok);
                                          smt_ok = (uu___159_7648.smt_ok);
                                          tcenv = (uu___159_7648.tcenv)
                                        }) in
                                   match uu____7647 with
                                   | Success uu____7650 ->
                                       let wl1 =
                                         let uu___160_7652 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___160_7652.wl_deferred);
                                           ctr = (uu___160_7652.ctr);
                                           defer_ok =
                                             (uu___160_7652.defer_ok);
                                           smt_ok = (uu___160_7652.smt_ok);
                                           tcenv = (uu___160_7652.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1 in
                                       let uu____7654 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds in
                                       Some wl2
                                   | uu____7657 -> None))))
                   | uu____7658 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____7723 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____7723
                      then
                        let uu____7724 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7724
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___161_7756 = hd1 in
                      let uu____7757 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_7756.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_7756.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7757
                      } in
                    let hd21 =
                      let uu___162_7761 = hd2 in
                      let uu____7762 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___162_7761.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___162_7761.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7762
                      } in
                    let prob =
                      let uu____7766 =
                        let uu____7769 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7769 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_48  -> FStar_TypeChecker_Common.TProb _0_48)
                        uu____7766 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____7777 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7777 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____7780 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____7780 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7798 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives.fst in
                           let uu____7801 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____7798 uu____7801 in
                         ((let uu____7807 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____7807
                           then
                             let uu____7808 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____7809 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7808 uu____7809
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7824 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____7830 = aux scope env [] bs1 bs2 in
              match uu____7830 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7846 = compress_tprob wl problem in
        solve_t' env uu____7846 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7879 = head_matches_delta env1 wl1 t1 t2 in
          match uu____7879 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7896,uu____7897) ->
                   let may_relate head3 =
                     let uu____7912 =
                       let uu____7913 = FStar_Syntax_Util.un_uinst head3 in
                       uu____7913.FStar_Syntax_Syntax.n in
                     match uu____7912 with
                     | FStar_Syntax_Syntax.Tm_name uu____7916 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____7917 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____7934 -> false in
                   let uu____7935 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____7935
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
                                let uu____7952 =
                                  let uu____7953 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____7953 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____7952 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____7955 = solve_prob orig (Some guard) [] wl1 in
                     solve env1 uu____7955
                   else
                     (let uu____7957 =
                        let uu____7958 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____7959 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____7958 uu____7959 in
                      giveup env1 uu____7957 orig)
               | (uu____7960,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___163_7968 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___163_7968.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___163_7968.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___163_7968.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___163_7968.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___163_7968.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___163_7968.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___163_7968.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___163_7968.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____7969,None ) ->
                   ((let uu____7976 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____7976
                     then
                       let uu____7977 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____7978 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____7979 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____7980 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____7977
                         uu____7978 uu____7979 uu____7980
                     else ());
                    (let uu____7982 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____7982 with
                     | (head11,args1) ->
                         let uu____8008 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____8008 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8048 =
                                  let uu____8049 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____8050 = args_to_string args1 in
                                  let uu____8051 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____8052 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8049 uu____8050 uu____8051
                                    uu____8052 in
                                giveup env1 uu____8048 orig
                              else
                                (let uu____8054 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8057 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____8057 = FStar_Syntax_Util.Equal) in
                                 if uu____8054
                                 then
                                   let uu____8058 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____8058 with
                                   | USolved wl2 ->
                                       let uu____8060 =
                                         solve_prob orig None [] wl2 in
                                       solve env1 uu____8060
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8064 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____8064 with
                                    | (base1,refinement1) ->
                                        let uu____8090 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____8090 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____8144 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____8144 with
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
                                                           (fun uu____8154 
                                                              ->
                                                              fun uu____8155 
                                                                ->
                                                                match 
                                                                  (uu____8154,
                                                                    uu____8155)
                                                                with
                                                                | ((a,uu____8165),
                                                                   (a',uu____8167))
                                                                    ->
                                                                    let uu____8172
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
                                                                    uu____8172)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____8178 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8178 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8182 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___164_8215 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___164_8215.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___164_8215.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___164_8215.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___164_8215.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___164_8215.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___164_8215.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___164_8215.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___164_8215.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____8235 = p in
          match uu____8235 with
          | (((u,k),xs,c),ps,(h,uu____8246,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8295 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____8295 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8309 = h gs_xs in
                     let uu____8310 =
                       let uu____8317 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_50  -> FStar_Util.Inl _0_50) in
                       FStar_All.pipe_right uu____8317
                         (fun _0_51  -> Some _0_51) in
                     FStar_Syntax_Util.abs xs1 uu____8309 uu____8310 in
                   ((let uu____8348 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8348
                     then
                       let uu____8349 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____8350 = FStar_Syntax_Print.comp_to_string c in
                       let uu____8351 = FStar_Syntax_Print.term_to_string im in
                       let uu____8352 = FStar_Syntax_Print.tag_of_term im in
                       let uu____8353 =
                         let uu____8354 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____8354
                           (FStar_String.concat ", ") in
                       let uu____8357 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8349 uu____8350 uu____8351 uu____8352
                         uu____8353 uu____8357
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___130_8375 =
          match uu___130_8375 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____8404 = p in
          match uu____8404 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8462 = FStar_List.nth ps i in
              (match uu____8462 with
               | (pi,uu____8465) ->
                   let uu____8470 = FStar_List.nth xs i in
                   (match uu____8470 with
                    | (xi,uu____8477) ->
                        let rec gs k =
                          let uu____8486 = FStar_Syntax_Util.arrow_formals k in
                          match uu____8486 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8538)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8546 = new_uvar r xs k_a in
                                    (match uu____8546 with
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
                                         let uu____8565 = aux subst2 tl1 in
                                         (match uu____8565 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8580 =
                                                let uu____8582 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8582 :: gi_xs' in
                                              let uu____8583 =
                                                let uu____8585 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8585 :: gi_ps' in
                                              (uu____8580, uu____8583))) in
                              aux [] bs in
                        let uu____8588 =
                          let uu____8589 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8589 in
                        if uu____8588
                        then None
                        else
                          (let uu____8592 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8592 with
                           | (g_xs,uu____8599) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8606 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r in
                                 let uu____8611 =
                                   let uu____8618 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_52  -> FStar_Util.Inl _0_52) in
                                   FStar_All.pipe_right uu____8618
                                     (fun _0_53  -> Some _0_53) in
                                 FStar_Syntax_Util.abs xs uu____8606
                                   uu____8611 in
                               let sub1 =
                                 let uu____8649 =
                                   let uu____8652 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let uu____8659 =
                                     let uu____8662 =
                                       FStar_List.map
                                         (fun uu____8668  ->
                                            match uu____8668 with
                                            | (uu____8673,uu____8674,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____8662 in
                                   mk_problem (p_scope orig) orig uu____8652
                                     (p_rel orig) uu____8659 None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_54  ->
                                      FStar_TypeChecker_Common.TProb _0_54)
                                   uu____8649 in
                               ((let uu____8684 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____8684
                                 then
                                   let uu____8685 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____8686 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8685 uu____8686
                                 else ());
                                (let wl2 =
                                   let uu____8689 =
                                     let uu____8691 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives.fst (p_guard sub1) in
                                     Some uu____8691 in
                                   solve_prob orig uu____8689
                                     [TERM (u, proj)] wl1 in
                                 let uu____8696 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_55  -> Some _0_55) uu____8696))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8720 = lhs in
          match uu____8720 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8743 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____8743 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8765 =
                        let uu____8791 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____8791) in
                      Some uu____8765
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____8874 =
                           let uu____8878 =
                             let uu____8879 = FStar_Syntax_Subst.compress k in
                             uu____8879.FStar_Syntax_Syntax.n in
                           (uu____8878, args) in
                         match uu____8874 with
                         | (uu____8886,[]) ->
                             let uu____8888 =
                               let uu____8894 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____8894) in
                             Some uu____8888
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____8905,uu____8906) ->
                             let uu____8917 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____8917 with
                              | (uv1,uv_args) ->
                                  let uu____8946 =
                                    let uu____8947 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____8947.FStar_Syntax_Syntax.n in
                                  (match uu____8946 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____8954) ->
                                       let uu____8967 =
                                         pat_vars env [] uv_args in
                                       (match uu____8967 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____8981  ->
                                                      let uu____8982 =
                                                        let uu____8983 =
                                                          let uu____8984 =
                                                            let uu____8987 =
                                                              let uu____8988
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____8988
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____8987 in
                                                          fst uu____8984 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____8983 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____8982)) in
                                            let c1 =
                                              let uu____8994 =
                                                let uu____8995 =
                                                  let uu____8998 =
                                                    let uu____8999 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____8999
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____8998 in
                                                fst uu____8995 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____8994 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9008 =
                                                let uu____9015 =
                                                  let uu____9021 =
                                                    let uu____9022 =
                                                      let uu____9025 =
                                                        let uu____9026 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9026
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9025 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9022 in
                                                  FStar_Util.Inl uu____9021 in
                                                Some uu____9015 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9008 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9046 -> None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9049,uu____9050)
                             ->
                             let uu____9062 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9062 with
                              | (uv1,uv_args) ->
                                  let uu____9091 =
                                    let uu____9092 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9092.FStar_Syntax_Syntax.n in
                                  (match uu____9091 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9099) ->
                                       let uu____9112 =
                                         pat_vars env [] uv_args in
                                       (match uu____9112 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9126  ->
                                                      let uu____9127 =
                                                        let uu____9128 =
                                                          let uu____9129 =
                                                            let uu____9132 =
                                                              let uu____9133
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9133
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9132 in
                                                          fst uu____9129 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9128 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9127)) in
                                            let c1 =
                                              let uu____9139 =
                                                let uu____9140 =
                                                  let uu____9143 =
                                                    let uu____9144 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9144
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9143 in
                                                fst uu____9140 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9139 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9153 =
                                                let uu____9160 =
                                                  let uu____9166 =
                                                    let uu____9167 =
                                                      let uu____9170 =
                                                        let uu____9171 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9171
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9170 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9167 in
                                                  FStar_Util.Inl uu____9166 in
                                                Some uu____9160 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9153 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9191 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9196)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____9222 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____9222
                                 (fun _0_56  -> Some _0_56)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9241 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____9241 with
                                  | (args1,rest) ->
                                      let uu____9257 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____9257 with
                                       | (xs2,c2) ->
                                           let uu____9265 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____9265
                                             (fun uu____9276  ->
                                                match uu____9276 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9298 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____9298 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____9344 =
                                        let uu____9347 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9347 in
                                      FStar_All.pipe_right uu____9344
                                        (fun _0_57  -> Some _0_57))
                         | uu____9355 ->
                             let uu____9359 =
                               let uu____9360 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____9361 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____9362 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9360 uu____9361 uu____9362 in
                             failwith uu____9359 in
                       let uu____9366 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____9366
                         (fun uu____9394  ->
                            match uu____9394 with
                            | (xs1,c1) ->
                                let uu____9422 =
                                  let uu____9445 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9445) in
                                Some uu____9422)) in
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
                     let uu____9517 = imitate orig env wl1 st in
                     match uu____9517 with
                     | Failed uu____9522 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9528 = project orig env wl1 i st in
                      match uu____9528 with
                      | None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some (Failed uu____9535) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____9549 = FStar_Syntax_Util.head_and_args t21 in
                match uu____9549 with
                | (hd1,uu____9560) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9575 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9583 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9584 -> true
                     | uu____9599 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____9602 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____9602
                         then true
                         else
                           ((let uu____9605 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____9605
                             then
                               let uu____9606 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9606
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9614 =
                    let uu____9617 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____9617 FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____9614 FStar_Syntax_Free.names in
                let uu____9648 = FStar_Util.set_is_empty fvs_hd in
                if uu____9648
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____9657 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____9657 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9665 =
                            let uu____9666 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____9666 in
                          giveup_or_defer1 orig uu____9665
                        else
                          (let uu____9668 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____9668
                           then
                             let uu____9669 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____9669
                              then
                                let uu____9670 = subterms args_lhs in
                                imitate' orig env wl1 uu____9670
                              else
                                ((let uu____9674 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____9674
                                  then
                                    let uu____9675 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____9676 = names_to_string fvs1 in
                                    let uu____9677 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9675 uu____9676 uu____9677
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9682 ->
                                        let uu____9683 = sn_binders env vars in
                                        u_abs k_uv uu____9683 t21 in
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
                               (let uu____9692 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____9692
                                then
                                  ((let uu____9694 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____9694
                                    then
                                      let uu____9695 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____9696 = names_to_string fvs1 in
                                      let uu____9697 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9695 uu____9696 uu____9697
                                    else ());
                                   (let uu____9699 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9699
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
                     (let uu____9710 =
                        let uu____9711 = FStar_Syntax_Free.names t1 in
                        check_head uu____9711 t2 in
                      if uu____9710
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____9715 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____9715
                          then
                            let uu____9716 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9716
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9719 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9719 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9761 =
               match uu____9761 with
               | (t,u,k,args) ->
                   let uu____9791 = FStar_Syntax_Util.arrow_formals k in
                   (match uu____9791 with
                    | (all_formals,uu____9802) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____9894  ->
                                        match uu____9894 with
                                        | (x,imp) ->
                                            let uu____9901 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____9901, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____9909 = FStar_Syntax_Util.type_u () in
                                match uu____9909 with
                                | (t1,uu____9913) ->
                                    let uu____9914 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    fst uu____9914 in
                              let uu____9917 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____9917 with
                               | (t',tm_u1) ->
                                   let uu____9924 = destruct_flex_t t' in
                                   (match uu____9924 with
                                    | (uu____9944,u1,k1,uu____9947) ->
                                        let sol =
                                          let uu____9975 =
                                            let uu____9980 =
                                              u_abs k all_formals t' in
                                            ((u, k), uu____9980) in
                                          TERM uu____9975 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k1, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10040 = pat_var_opt env pat_args hd1 in
                              (match uu____10040 with
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
                                              (fun uu____10069  ->
                                                 match uu____10069 with
                                                 | (x,uu____10073) ->
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
                                      let uu____10079 =
                                        let uu____10080 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____10080 in
                                      if uu____10079
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10084 =
                                           FStar_Util.set_add (fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10084 formals1
                                           tl1)))
                          | uu____10090 -> failwith "Impossible" in
                        let uu____10101 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____10101 all_formals args) in
             let solve_both_pats wl1 uu____10141 uu____10142 r =
               match (uu____10141, uu____10142) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10256 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____10256
                   then
                     let uu____10257 = solve_prob orig None [] wl1 in
                     solve env uu____10257
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____10272 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____10272
                       then
                         let uu____10273 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____10274 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____10275 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____10276 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____10277 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10273 uu____10274 uu____10275 uu____10276
                           uu____10277
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____10319 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____10319 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10327 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____10327 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10357 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10357 in
                                  let uu____10360 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____10360 k3)
                           else
                             (let uu____10363 =
                                let uu____10364 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____10365 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____10366 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10364 uu____10365 uu____10366 in
                              failwith uu____10363) in
                       let uu____10367 =
                         let uu____10373 =
                           let uu____10381 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____10381 in
                         match uu____10373 with
                         | (bs,k1') ->
                             let uu____10399 =
                               let uu____10407 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____10407 in
                             (match uu____10399 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____10428 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_58  ->
                                         FStar_TypeChecker_Common.TProb _0_58)
                                      uu____10428 in
                                  let uu____10433 =
                                    let uu____10436 =
                                      let uu____10437 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____10437.FStar_Syntax_Syntax.n in
                                    let uu____10440 =
                                      let uu____10441 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____10441.FStar_Syntax_Syntax.n in
                                    (uu____10436, uu____10440) in
                                  (match uu____10433 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10449,uu____10450) ->
                                       (k1', [sub_prob])
                                   | (uu____10454,FStar_Syntax_Syntax.Tm_type
                                      uu____10455) -> (k2', [sub_prob])
                                   | uu____10459 ->
                                       let uu____10462 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____10462 with
                                        | (t,uu____10471) ->
                                            let uu____10472 = new_uvar r zs t in
                                            (match uu____10472 with
                                             | (k_zs,uu____10481) ->
                                                 let kprob =
                                                   let uu____10483 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_59  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_59) uu____10483 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____10367 with
                       | (k_u',sub_probs) ->
                           let uu____10497 =
                             let uu____10505 =
                               let uu____10506 = new_uvar r zs k_u' in
                               FStar_All.pipe_left FStar_Pervasives.fst
                                 uu____10506 in
                             let uu____10511 =
                               let uu____10514 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____10514 in
                             let uu____10517 =
                               let uu____10520 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____10520 in
                             (uu____10505, uu____10511, uu____10517) in
                           (match uu____10497 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____10539 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____10539 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____10551 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____10551
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____10555 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____10555 with
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
             let solve_one_pat uu____10587 uu____10588 =
               match (uu____10587, uu____10588) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10652 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____10652
                     then
                       let uu____10653 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10654 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10653 uu____10654
                     else ());
                    (let uu____10656 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____10656
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10663  ->
                              fun uu____10664  ->
                                match (uu____10663, uu____10664) with
                                | ((a,uu____10674),(t21,uu____10676)) ->
                                    let uu____10681 =
                                      let uu____10684 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____10684
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____10681
                                      (fun _0_60  ->
                                         FStar_TypeChecker_Common.TProb _0_60))
                           xs args2 in
                       let guard =
                         let uu____10688 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____10688 in
                       let wl1 = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____10698 = occurs_check env wl (u1, k1) t21 in
                        match uu____10698 with
                        | (occurs_ok,uu____10703) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____10708 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____10708
                            then
                              let sol =
                                let uu____10710 =
                                  let uu____10715 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____10715) in
                                TERM uu____10710 in
                              let wl1 = solve_prob orig None [sol] wl in
                              solve env wl1
                            else
                              (let uu____10720 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____10720
                               then
                                 let uu____10721 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____10721 with
                                 | (sol,(uu____10731,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____10741 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____10741
                                       then
                                         let uu____10742 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10742
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10747 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____10749 = lhs in
             match uu____10749 with
             | (t1,u1,k1,args1) ->
                 let uu____10754 = rhs in
                 (match uu____10754 with
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
                       | uu____10780 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____10786 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____10786 with
                              | (sol,uu____10793) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____10796 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____10796
                                    then
                                      let uu____10797 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____10797
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____10802 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____10804 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____10804
        then
          let uu____10805 = solve_prob orig None [] wl in
          solve env uu____10805
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____10809 = FStar_Util.physical_equality t1 t2 in
           if uu____10809
           then
             let uu____10810 = solve_prob orig None [] wl in
             solve env uu____10810
           else
             ((let uu____10813 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____10813
               then
                 let uu____10814 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____10814
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____10817,uu____10818) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____10819,FStar_Syntax_Syntax.Tm_bvar uu____10820) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___131_10860 =
                     match uu___131_10860 with
                     | [] -> c
                     | bs ->
                         let uu____10874 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c)) None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____10874 in
                   let uu____10884 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____10884 with
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
                                   let uu____10970 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____10970
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____10972 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.CProb _0_61)
                                   uu____10972))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___132_11049 =
                     match uu___132_11049 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l)) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____11084 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____11084 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11167 =
                                   let uu____11170 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____11171 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____11170
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11171 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_TypeChecker_Common.TProb _0_62)
                                   uu____11167))
               | (FStar_Syntax_Syntax.Tm_abs uu____11174,uu____11175) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11198 -> true
                     | uu____11213 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11241 =
                     let uu____11252 = maybe_eta t1 in
                     let uu____11257 = maybe_eta t2 in
                     (uu____11252, uu____11257) in
                   (match uu____11241 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___165_11288 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___165_11288.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___165_11288.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___165_11288.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___165_11288.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___165_11288.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___165_11288.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___165_11288.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___165_11288.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11307 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11307
                        then
                          let uu____11308 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11308 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11329 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11329
                        then
                          let uu____11330 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11330 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11335 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11346,FStar_Syntax_Syntax.Tm_abs uu____11347) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11370 -> true
                     | uu____11385 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11413 =
                     let uu____11424 = maybe_eta t1 in
                     let uu____11429 = maybe_eta t2 in
                     (uu____11424, uu____11429) in
                   (match uu____11413 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___165_11460 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___165_11460.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___165_11460.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___165_11460.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___165_11460.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___165_11460.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___165_11460.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___165_11460.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___165_11460.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11479 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11479
                        then
                          let uu____11480 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11480 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11501 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11501
                        then
                          let uu____11502 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11502 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11507 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11518,FStar_Syntax_Syntax.Tm_refine uu____11519) ->
                   let uu____11528 = as_refinement env wl t1 in
                   (match uu____11528 with
                    | (x1,phi1) ->
                        let uu____11533 = as_refinement env wl t2 in
                        (match uu____11533 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11539 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_63  ->
                                    FStar_TypeChecker_Common.TProb _0_63)
                                 uu____11539 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____11572 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____11572
                                 (guard_on_element wl problem x11) in
                             let fallback uu____11576 =
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
                                 let uu____11582 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____11582 impl in
                               let wl1 = solve_prob orig (Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11589 =
                                   let uu____11592 =
                                     let uu____11593 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____11593 :: (p_scope orig) in
                                   mk_problem uu____11592 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____11589 in
                               let uu____11596 =
                                 solve env1
                                   (let uu___166_11597 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___166_11597.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___166_11597.smt_ok);
                                      tcenv = (uu___166_11597.tcenv)
                                    }) in
                               (match uu____11596 with
                                | Failed uu____11601 -> fallback ()
                                | Success uu____11604 ->
                                    let guard =
                                      let uu____11608 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives.fst in
                                      let uu____11611 =
                                        let uu____11612 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives.fst in
                                        FStar_All.pipe_right uu____11612
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____11608
                                        uu____11611 in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl2 =
                                      let uu___167_11619 = wl1 in
                                      {
                                        attempting =
                                          (uu___167_11619.attempting);
                                        wl_deferred =
                                          (uu___167_11619.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___167_11619.defer_ok);
                                        smt_ok = (uu___167_11619.smt_ok);
                                        tcenv = (uu___167_11619.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11621,FStar_Syntax_Syntax.Tm_uvar uu____11622) ->
                   let uu____11639 = destruct_flex_t t1 in
                   let uu____11640 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11639 uu____11640
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11641;
                     FStar_Syntax_Syntax.tk = uu____11642;
                     FStar_Syntax_Syntax.pos = uu____11643;
                     FStar_Syntax_Syntax.vars = uu____11644;_},uu____11645),FStar_Syntax_Syntax.Tm_uvar
                  uu____11646) ->
                   let uu____11677 = destruct_flex_t t1 in
                   let uu____11678 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11677 uu____11678
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11679,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11680;
                     FStar_Syntax_Syntax.tk = uu____11681;
                     FStar_Syntax_Syntax.pos = uu____11682;
                     FStar_Syntax_Syntax.vars = uu____11683;_},uu____11684))
                   ->
                   let uu____11715 = destruct_flex_t t1 in
                   let uu____11716 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11715 uu____11716
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11717;
                     FStar_Syntax_Syntax.tk = uu____11718;
                     FStar_Syntax_Syntax.pos = uu____11719;
                     FStar_Syntax_Syntax.vars = uu____11720;_},uu____11721),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11722;
                     FStar_Syntax_Syntax.tk = uu____11723;
                     FStar_Syntax_Syntax.pos = uu____11724;
                     FStar_Syntax_Syntax.vars = uu____11725;_},uu____11726))
                   ->
                   let uu____11771 = destruct_flex_t t1 in
                   let uu____11772 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11771 uu____11772
               | (FStar_Syntax_Syntax.Tm_uvar uu____11773,uu____11774) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11783 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11783 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11787;
                     FStar_Syntax_Syntax.tk = uu____11788;
                     FStar_Syntax_Syntax.pos = uu____11789;
                     FStar_Syntax_Syntax.vars = uu____11790;_},uu____11791),uu____11792)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11815 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11815 t2 wl
               | (uu____11819,FStar_Syntax_Syntax.Tm_uvar uu____11820) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____11829,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11830;
                     FStar_Syntax_Syntax.tk = uu____11831;
                     FStar_Syntax_Syntax.pos = uu____11832;
                     FStar_Syntax_Syntax.vars = uu____11833;_},uu____11834))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11857,FStar_Syntax_Syntax.Tm_type uu____11858) ->
                   solve_t' env
                     (let uu___168_11867 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_11867.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_11867.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_11867.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_11867.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_11867.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_11867.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_11867.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_11867.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_11867.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11868;
                     FStar_Syntax_Syntax.tk = uu____11869;
                     FStar_Syntax_Syntax.pos = uu____11870;
                     FStar_Syntax_Syntax.vars = uu____11871;_},uu____11872),FStar_Syntax_Syntax.Tm_type
                  uu____11873) ->
                   solve_t' env
                     (let uu___168_11896 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_11896.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_11896.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_11896.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_11896.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_11896.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_11896.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_11896.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_11896.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_11896.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11897,FStar_Syntax_Syntax.Tm_arrow uu____11898) ->
                   solve_t' env
                     (let uu___168_11914 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_11914.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_11914.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_11914.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_11914.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_11914.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_11914.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_11914.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_11914.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_11914.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11915;
                     FStar_Syntax_Syntax.tk = uu____11916;
                     FStar_Syntax_Syntax.pos = uu____11917;
                     FStar_Syntax_Syntax.vars = uu____11918;_},uu____11919),FStar_Syntax_Syntax.Tm_arrow
                  uu____11920) ->
                   solve_t' env
                     (let uu___168_11950 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_11950.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_11950.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_11950.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_11950.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_11950.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_11950.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_11950.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_11950.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_11950.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____11951,uu____11952) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____11963 =
                        let uu____11964 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____11964 in
                      if uu____11963
                      then
                        let uu____11965 =
                          FStar_All.pipe_left
                            (fun _0_65  ->
                               FStar_TypeChecker_Common.TProb _0_65)
                            (let uu___169_11968 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_11968.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_11968.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_11968.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_11968.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_11968.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___169_11968.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_11968.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_11968.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_11968.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____11969 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____11965 uu____11969 t2
                          wl
                      else
                        (let uu____11974 = base_and_refinement env wl t2 in
                         match uu____11974 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12004 =
                                    FStar_All.pipe_left
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66)
                                      (let uu___170_12007 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___170_12007.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___170_12007.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___170_12007.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___170_12007.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___170_12007.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___170_12007.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___170_12007.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___170_12007.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___170_12007.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12008 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12004
                                    uu____12008 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___171_12023 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___171_12023.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___171_12023.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12026 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67)
                                      uu____12026 in
                                  let guard =
                                    let uu____12034 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12034
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12040;
                     FStar_Syntax_Syntax.tk = uu____12041;
                     FStar_Syntax_Syntax.pos = uu____12042;
                     FStar_Syntax_Syntax.vars = uu____12043;_},uu____12044),uu____12045)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12070 =
                        let uu____12071 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12071 in
                      if uu____12070
                      then
                        let uu____12072 =
                          FStar_All.pipe_left
                            (fun _0_68  ->
                               FStar_TypeChecker_Common.TProb _0_68)
                            (let uu___169_12075 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_12075.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_12075.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_12075.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_12075.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_12075.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___169_12075.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_12075.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_12075.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_12075.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12076 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12072 uu____12076 t2
                          wl
                      else
                        (let uu____12081 = base_and_refinement env wl t2 in
                         match uu____12081 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12111 =
                                    FStar_All.pipe_left
                                      (fun _0_69  ->
                                         FStar_TypeChecker_Common.TProb _0_69)
                                      (let uu___170_12114 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___170_12114.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___170_12114.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___170_12114.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___170_12114.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___170_12114.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___170_12114.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___170_12114.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___170_12114.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___170_12114.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12115 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12111
                                    uu____12115 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___171_12130 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___171_12130.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___171_12130.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12133 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_70  ->
                                         FStar_TypeChecker_Common.TProb _0_70)
                                      uu____12133 in
                                  let guard =
                                    let uu____12141 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12141
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12147,FStar_Syntax_Syntax.Tm_uvar uu____12148) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12158 = base_and_refinement env wl t1 in
                      match uu____12158 with
                      | (t_base,uu____12169) ->
                          solve_t env
                            (let uu___172_12184 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___172_12184.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___172_12184.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___172_12184.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___172_12184.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___172_12184.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___172_12184.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___172_12184.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___172_12184.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12187,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12188;
                     FStar_Syntax_Syntax.tk = uu____12189;
                     FStar_Syntax_Syntax.pos = uu____12190;
                     FStar_Syntax_Syntax.vars = uu____12191;_},uu____12192))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12216 = base_and_refinement env wl t1 in
                      match uu____12216 with
                      | (t_base,uu____12227) ->
                          solve_t env
                            (let uu___172_12242 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___172_12242.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___172_12242.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___172_12242.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___172_12242.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___172_12242.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___172_12242.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___172_12242.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___172_12242.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12245,uu____12246) ->
                   let t21 =
                     let uu____12254 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____12254 in
                   solve_t env
                     (let uu___173_12267 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_12267.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___173_12267.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___173_12267.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___173_12267.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_12267.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_12267.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_12267.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_12267.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_12267.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12268,FStar_Syntax_Syntax.Tm_refine uu____12269) ->
                   let t11 =
                     let uu____12277 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____12277 in
                   solve_t env
                     (let uu___174_12290 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_12290.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___174_12290.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___174_12290.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___174_12290.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_12290.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_12290.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_12290.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_12290.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_12290.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12293,uu____12294) ->
                   let head1 =
                     let uu____12313 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12313 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12344 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12344 FStar_Pervasives.fst in
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
                          then None
                          else
                            (let uu____12392 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_71  -> Some _0_71)
                               uu____12392) in
                        let uu____12394 = solve_prob orig guard [] wl in
                        solve env uu____12394
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12397,uu____12398) ->
                   let head1 =
                     let uu____12406 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12406 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12437 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12437 FStar_Pervasives.fst in
                   let uu____12465 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12465
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12474 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12474
                      then
                        let guard =
                          let uu____12481 =
                            let uu____12482 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12482 = FStar_Syntax_Util.Equal in
                          if uu____12481
                          then None
                          else
                            (let uu____12485 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_72  -> Some _0_72)
                               uu____12485) in
                        let uu____12487 = solve_prob orig guard [] wl in
                        solve env uu____12487
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12490,uu____12491) ->
                   let head1 =
                     let uu____12495 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12495 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12526 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12526 FStar_Pervasives.fst in
                   let uu____12554 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12554
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12563 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12563
                      then
                        let guard =
                          let uu____12570 =
                            let uu____12571 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12571 = FStar_Syntax_Util.Equal in
                          if uu____12570
                          then None
                          else
                            (let uu____12574 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_73  -> Some _0_73)
                               uu____12574) in
                        let uu____12576 = solve_prob orig guard [] wl in
                        solve env uu____12576
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12579,uu____12580) ->
                   let head1 =
                     let uu____12584 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12584 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12615 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12615 FStar_Pervasives.fst in
                   let uu____12643 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12643
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12652 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12652
                      then
                        let guard =
                          let uu____12659 =
                            let uu____12660 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12660 = FStar_Syntax_Util.Equal in
                          if uu____12659
                          then None
                          else
                            (let uu____12663 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_74  -> Some _0_74)
                               uu____12663) in
                        let uu____12665 = solve_prob orig guard [] wl in
                        solve env uu____12665
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____12668,uu____12669) ->
                   let head1 =
                     let uu____12673 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12673 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12704 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12704 FStar_Pervasives.fst in
                   let uu____12732 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12732
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12741 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12741
                      then
                        let guard =
                          let uu____12748 =
                            let uu____12749 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12749 = FStar_Syntax_Util.Equal in
                          if uu____12748
                          then None
                          else
                            (let uu____12752 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_75  -> Some _0_75)
                               uu____12752) in
                        let uu____12754 = solve_prob orig guard [] wl in
                        solve env uu____12754
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____12757,uu____12758) ->
                   let head1 =
                     let uu____12771 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12771 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12802 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12802 FStar_Pervasives.fst in
                   let uu____12830 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12830
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12839 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12839
                      then
                        let guard =
                          let uu____12846 =
                            let uu____12847 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12847 = FStar_Syntax_Util.Equal in
                          if uu____12846
                          then None
                          else
                            (let uu____12850 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_76  -> Some _0_76)
                               uu____12850) in
                        let uu____12852 = solve_prob orig guard [] wl in
                        solve env uu____12852
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12855,FStar_Syntax_Syntax.Tm_match uu____12856) ->
                   let head1 =
                     let uu____12875 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12875 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12906 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12906 FStar_Pervasives.fst in
                   let uu____12934 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12934
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12943 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12943
                      then
                        let guard =
                          let uu____12950 =
                            let uu____12951 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12951 = FStar_Syntax_Util.Equal in
                          if uu____12950
                          then None
                          else
                            (let uu____12954 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_77  -> Some _0_77)
                               uu____12954) in
                        let uu____12956 = solve_prob orig guard [] wl in
                        solve env uu____12956
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12959,FStar_Syntax_Syntax.Tm_uinst uu____12960) ->
                   let head1 =
                     let uu____12968 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12968 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12999 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12999 FStar_Pervasives.fst in
                   let uu____13027 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13027
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13036 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13036
                      then
                        let guard =
                          let uu____13043 =
                            let uu____13044 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13044 = FStar_Syntax_Util.Equal in
                          if uu____13043
                          then None
                          else
                            (let uu____13047 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_78  -> Some _0_78)
                               uu____13047) in
                        let uu____13049 = solve_prob orig guard [] wl in
                        solve env uu____13049
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13052,FStar_Syntax_Syntax.Tm_name uu____13053) ->
                   let head1 =
                     let uu____13057 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13057 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13088 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13088 FStar_Pervasives.fst in
                   let uu____13116 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13116
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13125 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13125
                      then
                        let guard =
                          let uu____13132 =
                            let uu____13133 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13133 = FStar_Syntax_Util.Equal in
                          if uu____13132
                          then None
                          else
                            (let uu____13136 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_79  -> Some _0_79)
                               uu____13136) in
                        let uu____13138 = solve_prob orig guard [] wl in
                        solve env uu____13138
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13141,FStar_Syntax_Syntax.Tm_constant uu____13142) ->
                   let head1 =
                     let uu____13146 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13146 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13177 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13177 FStar_Pervasives.fst in
                   let uu____13205 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13205
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13214 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13214
                      then
                        let guard =
                          let uu____13221 =
                            let uu____13222 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13222 = FStar_Syntax_Util.Equal in
                          if uu____13221
                          then None
                          else
                            (let uu____13225 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_80  -> Some _0_80)
                               uu____13225) in
                        let uu____13227 = solve_prob orig guard [] wl in
                        solve env uu____13227
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13230,FStar_Syntax_Syntax.Tm_fvar uu____13231) ->
                   let head1 =
                     let uu____13235 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13235 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13266 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13266 FStar_Pervasives.fst in
                   let uu____13294 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13294
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13303 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13303
                      then
                        let guard =
                          let uu____13310 =
                            let uu____13311 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13311 = FStar_Syntax_Util.Equal in
                          if uu____13310
                          then None
                          else
                            (let uu____13314 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_81  -> Some _0_81)
                               uu____13314) in
                        let uu____13316 = solve_prob orig guard [] wl in
                        solve env uu____13316
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13319,FStar_Syntax_Syntax.Tm_app uu____13320) ->
                   let head1 =
                     let uu____13333 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13333 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13364 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13364 FStar_Pervasives.fst in
                   let uu____13392 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13392
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13401 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13401
                      then
                        let guard =
                          let uu____13408 =
                            let uu____13409 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13409 = FStar_Syntax_Util.Equal in
                          if uu____13408
                          then None
                          else
                            (let uu____13412 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_82  -> Some _0_82)
                               uu____13412) in
                        let uu____13414 = solve_prob orig guard [] wl in
                        solve env uu____13414
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13418,uu____13419),uu____13420) ->
                   solve_t' env
                     (let uu___175_13449 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_13449.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_13449.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_13449.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_13449.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_13449.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_13449.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_13449.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_13449.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_13449.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13452,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13454,uu____13455)) ->
                   solve_t' env
                     (let uu___176_13484 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_13484.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___176_13484.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___176_13484.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___176_13484.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_13484.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_13484.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_13484.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_13484.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_13484.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13485,uu____13486) ->
                   let uu____13494 =
                     let uu____13495 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13496 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13495
                       uu____13496 in
                   failwith uu____13494
               | (FStar_Syntax_Syntax.Tm_meta uu____13497,uu____13498) ->
                   let uu____13503 =
                     let uu____13504 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13505 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13504
                       uu____13505 in
                   failwith uu____13503
               | (FStar_Syntax_Syntax.Tm_delayed uu____13506,uu____13507) ->
                   let uu____13528 =
                     let uu____13529 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13530 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13529
                       uu____13530 in
                   failwith uu____13528
               | (uu____13531,FStar_Syntax_Syntax.Tm_meta uu____13532) ->
                   let uu____13537 =
                     let uu____13538 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13539 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13538
                       uu____13539 in
                   failwith uu____13537
               | (uu____13540,FStar_Syntax_Syntax.Tm_delayed uu____13541) ->
                   let uu____13562 =
                     let uu____13563 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13564 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13563
                       uu____13564 in
                   failwith uu____13562
               | (uu____13565,FStar_Syntax_Syntax.Tm_let uu____13566) ->
                   let uu____13574 =
                     let uu____13575 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13576 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13575
                       uu____13576 in
                   failwith uu____13574
               | uu____13577 -> giveup env "head tag mismatch" orig)))
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
          (let uu____13609 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____13609
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____13617  ->
                  fun uu____13618  ->
                    match (uu____13617, uu____13618) with
                    | ((a1,uu____13628),(a2,uu____13630)) ->
                        let uu____13635 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_83  -> FStar_TypeChecker_Common.TProb _0_83)
                          uu____13635)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____13641 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p) FStar_Pervasives.fst)
                 sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____13641 in
           let wl1 = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____13661 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____13668)::[] -> wp1
              | uu____13681 ->
                  let uu____13687 =
                    let uu____13688 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____13688 in
                  failwith uu____13687 in
            let uu____13691 =
              let uu____13697 =
                let uu____13698 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____13698 in
              [uu____13697] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____13691;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____13699 = lift_c1 () in solve_eq uu____13699 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___133_13703  ->
                       match uu___133_13703 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____13704 -> false)) in
             let uu____13705 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____13729)::uu____13730,(wp2,uu____13732)::uu____13733)
                   -> (wp1, wp2)
               | uu____13774 ->
                   let uu____13787 =
                     let uu____13788 =
                       let uu____13791 =
                         let uu____13792 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____13793 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____13792 uu____13793 in
                       (uu____13791, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____13788 in
                   raise uu____13787 in
             match uu____13705 with
             | (wpc1,wpc2) ->
                 let uu____13810 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____13810
                 then
                   let uu____13813 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env uu____13813 wl
                 else
                   (let uu____13817 =
                      let uu____13821 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____13821 in
                    match uu____13817 with
                    | (c2_decl,qualifiers) ->
                        let uu____13833 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____13833
                        then
                          let c1_repr =
                            let uu____13836 =
                              let uu____13837 =
                                let uu____13838 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____13838 in
                              let uu____13839 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13837 uu____13839 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13836 in
                          let c2_repr =
                            let uu____13841 =
                              let uu____13842 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____13843 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13842 uu____13843 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13841 in
                          let prob =
                            let uu____13845 =
                              let uu____13848 =
                                let uu____13849 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____13850 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____13849
                                  uu____13850 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____13848 in
                            FStar_TypeChecker_Common.TProb uu____13845 in
                          let wl1 =
                            let uu____13852 =
                              let uu____13854 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives.fst in
                              Some uu____13854 in
                            solve_prob orig uu____13852 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____13861 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____13861
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____13863 =
                                     let uu____13866 =
                                       let uu____13867 =
                                         let uu____13877 =
                                           let uu____13878 =
                                             let uu____13879 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____13879] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____13878 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____13880 =
                                           let uu____13882 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____13883 =
                                             let uu____13885 =
                                               let uu____13886 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____13886 in
                                             [uu____13885] in
                                           uu____13882 :: uu____13883 in
                                         (uu____13877, uu____13880) in
                                       FStar_Syntax_Syntax.Tm_app uu____13867 in
                                     FStar_Syntax_Syntax.mk uu____13866 in
                                   uu____13863
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____13897 =
                                    let uu____13900 =
                                      let uu____13901 =
                                        let uu____13911 =
                                          let uu____13912 =
                                            let uu____13913 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____13913] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____13912 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____13914 =
                                          let uu____13916 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____13917 =
                                            let uu____13919 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____13920 =
                                              let uu____13922 =
                                                let uu____13923 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____13923 in
                                              [uu____13922] in
                                            uu____13919 :: uu____13920 in
                                          uu____13916 :: uu____13917 in
                                        (uu____13911, uu____13914) in
                                      FStar_Syntax_Syntax.Tm_app uu____13901 in
                                    FStar_Syntax_Syntax.mk uu____13900 in
                                  uu____13897
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____13934 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_TypeChecker_Common.TProb _0_84)
                               uu____13934 in
                           let wl1 =
                             let uu____13940 =
                               let uu____13942 =
                                 let uu____13945 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____13945 g in
                               FStar_All.pipe_left (fun _0_85  -> Some _0_85)
                                 uu____13942 in
                             solve_prob orig uu____13940 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____13955 = FStar_Util.physical_equality c1 c2 in
        if uu____13955
        then
          let uu____13956 = solve_prob orig None [] wl in
          solve env uu____13956
        else
          ((let uu____13959 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____13959
            then
              let uu____13960 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____13961 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____13960
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____13961
            else ());
           (let uu____13963 =
              let uu____13966 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____13967 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____13966, uu____13967) in
            match uu____13963 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____13971),FStar_Syntax_Syntax.Total
                    (t2,uu____13973)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____13986 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____13986 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____13989,FStar_Syntax_Syntax.Total uu____13990) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14002),FStar_Syntax_Syntax.Total
                    (t2,uu____14004)) ->
                     let uu____14017 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14017 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14021),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14023)) ->
                     let uu____14036 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14036 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14040),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14042)) ->
                     let uu____14055 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14055 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14058,FStar_Syntax_Syntax.Comp uu____14059) ->
                     let uu____14065 =
                       let uu___177_14068 = problem in
                       let uu____14071 =
                         let uu____14072 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14072 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14068.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14071;
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14068.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___177_14068.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___177_14068.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14068.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14068.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14068.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14068.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14068.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14065 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14073,FStar_Syntax_Syntax.Comp uu____14074) ->
                     let uu____14080 =
                       let uu___177_14083 = problem in
                       let uu____14086 =
                         let uu____14087 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14087 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14083.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14086;
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14083.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___177_14083.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___177_14083.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14083.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14083.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14083.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14083.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14083.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14080 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14088,FStar_Syntax_Syntax.GTotal uu____14089) ->
                     let uu____14095 =
                       let uu___178_14098 = problem in
                       let uu____14101 =
                         let uu____14102 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14102 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14098.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___178_14098.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14098.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14101;
                         FStar_TypeChecker_Common.element =
                           (uu___178_14098.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14098.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14098.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14098.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14098.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14098.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14095 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14103,FStar_Syntax_Syntax.Total uu____14104) ->
                     let uu____14110 =
                       let uu___178_14113 = problem in
                       let uu____14116 =
                         let uu____14117 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14117 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14113.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___178_14113.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14113.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14116;
                         FStar_TypeChecker_Common.element =
                           (uu___178_14113.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14113.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14113.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14113.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14113.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14113.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14110 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14118,FStar_Syntax_Syntax.Comp uu____14119) ->
                     let uu____14120 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____14120
                     then
                       let uu____14121 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type" in
                       solve_t env uu____14121 wl
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
                           (let uu____14131 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____14131
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14133 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____14133 with
                            | None  ->
                                let uu____14135 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14136 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____14136) in
                                if uu____14135
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
                                  (let uu____14139 =
                                     let uu____14140 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____14141 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14140 uu____14141 in
                                   giveup env uu____14139 orig)
                            | Some edge -> solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14146 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14162  ->
              match uu____14162 with
              | (uu____14169,uu____14170,u,uu____14172,uu____14173,uu____14174)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____14146 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14192 =
        FStar_All.pipe_right (fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____14192 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____14202 =
        FStar_All.pipe_right (snd ineqs)
          (FStar_List.map
             (fun uu____14214  ->
                match uu____14214 with
                | (u1,u2) ->
                    let uu____14219 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____14220 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____14219 uu____14220)) in
      FStar_All.pipe_right uu____14202 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14232,[])) -> "{}"
      | uu____14245 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14255 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____14255
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____14258 =
              FStar_List.map
                (fun uu____14262  ->
                   match uu____14262 with
                   | (uu____14265,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____14258 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____14269 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14269 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14307 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____14307
    then
      let uu____14308 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____14309 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14308
        (rel_to_string rel) uu____14309
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
            let uu____14329 =
              let uu____14331 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_86  -> Some _0_86) uu____14331 in
            FStar_Syntax_Syntax.new_bv uu____14329 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____14337 =
              let uu____14339 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_87  -> Some _0_87) uu____14339 in
            let uu____14341 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____14337 uu____14341 in
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
          let uu____14364 = FStar_Options.eager_inference () in
          if uu____14364
          then
            let uu___179_14365 = probs in
            {
              attempting = (uu___179_14365.attempting);
              wl_deferred = (uu___179_14365.wl_deferred);
              ctr = (uu___179_14365.ctr);
              defer_ok = false;
              smt_ok = (uu___179_14365.smt_ok);
              tcenv = (uu___179_14365.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Syntax_Unionfind.rollback tx;
             (let uu____14376 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____14376
              then
                let uu____14377 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____14377
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
          ((let uu____14387 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____14387
            then
              let uu____14388 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14388
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____14392 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____14392
             then
               let uu____14393 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14393
             else ());
            (let f2 =
               let uu____14396 =
                 let uu____14397 = FStar_Syntax_Util.unmeta f1 in
                 uu____14397.FStar_Syntax_Syntax.n in
               match uu____14396 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14401 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___180_14402 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___180_14402.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___180_14402.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___180_14402.FStar_TypeChecker_Env.implicits)
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
            let uu____14417 =
              let uu____14418 =
                let uu____14419 =
                  let uu____14420 =
                    FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____14420
                    (fun _0_88  -> FStar_TypeChecker_Common.NonTrivial _0_88) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14419;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____14418 in
            FStar_All.pipe_left (fun _0_89  -> Some _0_89) uu____14417
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____14453 =
        let uu____14454 =
          let uu____14455 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
          FStar_All.pipe_right uu____14455
            (fun _0_90  -> FStar_TypeChecker_Common.NonTrivial _0_90) in
        {
          FStar_TypeChecker_Env.guard_f = uu____14454;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      Some uu____14453
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
          (let uu____14481 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14481
           then
             let uu____14482 = FStar_Syntax_Print.term_to_string t1 in
             let uu____14483 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14482
               uu____14483
           else ());
          (let prob =
             let uu____14486 =
               let uu____14489 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____14489 in
             FStar_All.pipe_left
               (fun _0_91  -> FStar_TypeChecker_Common.TProb _0_91)
               uu____14486 in
           let g =
             let uu____14494 =
               let uu____14496 = singleton' env prob smt_ok in
               solve_and_commit env uu____14496 (fun uu____14497  -> None) in
             FStar_All.pipe_left (with_guard env prob) uu____14494 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14511 = try_teq true env t1 t2 in
        match uu____14511 with
        | None  ->
            let uu____14513 =
              let uu____14514 =
                let uu____14517 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                let uu____14518 = FStar_TypeChecker_Env.get_range env in
                (uu____14517, uu____14518) in
              FStar_Errors.Error uu____14514 in
            raise uu____14513
        | Some g ->
            ((let uu____14521 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____14521
              then
                let uu____14522 = FStar_Syntax_Print.term_to_string t1 in
                let uu____14523 = FStar_Syntax_Print.term_to_string t2 in
                let uu____14524 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14522
                  uu____14523 uu____14524
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
          (let uu____14540 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14540
           then
             let uu____14541 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____14542 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14541
               uu____14542
           else ());
          (let uu____14544 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____14544 with
           | (prob,x) ->
               let g =
                 let uu____14552 =
                   let uu____14554 = singleton' env prob smt_ok in
                   solve_and_commit env uu____14554
                     (fun uu____14555  -> None) in
                 FStar_All.pipe_left (with_guard env prob) uu____14552 in
               ((let uu____14561 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____14561
                 then
                   let uu____14562 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____14563 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____14564 =
                     let uu____14565 = FStar_Util.must g in
                     guard_to_string env uu____14565 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14562 uu____14563 uu____14564
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
          let uu____14589 = FStar_TypeChecker_Env.get_range env in
          let uu____14590 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.err uu____14589 uu____14590
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____14602 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____14602
         then
           let uu____14603 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____14604 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____14603
             uu____14604
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____14609 =
             let uu____14612 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None uu____14612 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_92  -> FStar_TypeChecker_Common.CProb _0_92) uu____14609 in
         let uu____14615 =
           let uu____14617 = singleton env prob in
           solve_and_commit env uu____14617 (fun uu____14618  -> None) in
         FStar_All.pipe_left (with_guard env prob) uu____14615)
let solve_universe_inequalities':
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____14637  ->
        match uu____14637 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____14662 =
                 let uu____14663 =
                   let uu____14666 =
                     let uu____14667 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____14668 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____14667 uu____14668 in
                   let uu____14669 = FStar_TypeChecker_Env.get_range env in
                   (uu____14666, uu____14669) in
                 FStar_Errors.Error uu____14663 in
               raise uu____14662) in
            let equiv1 v1 v' =
              let uu____14677 =
                let uu____14680 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____14681 = FStar_Syntax_Subst.compress_univ v' in
                (uu____14680, uu____14681) in
              match uu____14677 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____14688 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____14702 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____14702 with
                      | FStar_Syntax_Syntax.U_unif uu____14706 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____14717  ->
                                    match uu____14717 with
                                    | (u,v') ->
                                        let uu____14723 = equiv1 v1 v' in
                                        if uu____14723
                                        then
                                          let uu____14725 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____14725 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____14735 -> [])) in
            let uu____14738 =
              let wl =
                let uu___181_14741 = empty_worklist env in
                {
                  attempting = (uu___181_14741.attempting);
                  wl_deferred = (uu___181_14741.wl_deferred);
                  ctr = (uu___181_14741.ctr);
                  defer_ok = false;
                  smt_ok = (uu___181_14741.smt_ok);
                  tcenv = (uu___181_14741.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____14748  ->
                      match uu____14748 with
                      | (lb,v1) ->
                          let uu____14753 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____14753 with
                           | USolved wl1 -> ()
                           | uu____14755 -> fail lb v1))) in
            let rec check_ineq uu____14761 =
              match uu____14761 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____14768) -> true
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
                      uu____14779,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____14781,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____14786) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____14790,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____14795 -> false) in
            let uu____14798 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____14804  ->
                      match uu____14804 with
                      | (u,v1) ->
                          let uu____14809 = check_ineq (u, v1) in
                          if uu____14809
                          then true
                          else
                            ((let uu____14812 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____14812
                              then
                                let uu____14813 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____14814 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____14813
                                  uu____14814
                              else ());
                             false))) in
            if uu____14798
            then ()
            else
              ((let uu____14818 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____14818
                then
                  ((let uu____14820 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____14820);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____14826 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____14826))
                else ());
               (let uu____14832 =
                  let uu____14833 =
                    let uu____14836 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____14836) in
                  FStar_Errors.Error uu____14833 in
                raise uu____14832))
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
      let fail uu____14869 =
        match uu____14869 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____14879 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____14879
       then
         let uu____14880 = wl_to_string wl in
         let uu____14881 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____14880 uu____14881
       else ());
      (let g1 =
         let uu____14893 = solve_and_commit env wl fail in
         match uu____14893 with
         | Some [] ->
             let uu___182_14900 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___182_14900.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___182_14900.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___182_14900.FStar_TypeChecker_Env.implicits)
             }
         | uu____14903 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___183_14906 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___183_14906.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___183_14906.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___183_14906.FStar_TypeChecker_Env.implicits)
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
            let uu___184_14932 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___184_14932.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___184_14932.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___184_14932.FStar_TypeChecker_Env.implicits)
            } in
          let uu____14933 =
            let uu____14934 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____14934 in
          if uu____14933
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____14940 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____14940
                   then
                     let uu____14941 = FStar_TypeChecker_Env.get_range env in
                     let uu____14942 =
                       let uu____14943 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____14943 in
                     FStar_Errors.diag uu____14941 uu____14942
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding] env vc in
                   let uu____14946 = check_trivial vc1 in
                   match uu____14946 with
                   | FStar_TypeChecker_Common.Trivial  -> Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then None
                       else
                         ((let uu____14953 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____14953
                           then
                             let uu____14954 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____14955 =
                               let uu____14956 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____14956 in
                             FStar_Errors.diag uu____14954 uu____14955
                           else ());
                          (let vcs =
                             let uu____14962 = FStar_Options.use_tactics () in
                             if uu____14962
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)] in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____14976  ->
                                   match uu____14976 with
                                   | (env1,goal) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify]
                                           env1 goal in
                                       let uu____14982 = check_trivial goal1 in
                                       (match uu____14982 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____14984 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____14984
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                                               ();
                                             (let uu____14989 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____14989
                                              then
                                                let uu____14990 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____14991 =
                                                  let uu____14992 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____14993 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____14992 uu____14993 in
                                                FStar_Errors.diag uu____14990
                                                  uu____14991
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
      let uu____15001 = discharge_guard' None env g false in
      match uu____15001 with
      | Some g1 -> g1
      | None  ->
          let uu____15006 =
            let uu____15007 =
              let uu____15010 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____15010) in
            FStar_Errors.Error uu____15007 in
          raise uu____15006
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15017 = discharge_guard' None env g true in
      match uu____15017 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____15029 = FStar_Syntax_Unionfind.find u in
      match uu____15029 with | None  -> true | uu____15031 -> false in
    let rec until_fixpoint acc implicits =
      let uu____15044 = acc in
      match uu____15044 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____15090 = hd1 in
               (match uu____15090 with
                | (uu____15097,env,u,tm,k,r) ->
                    let uu____15103 = unresolved u in
                    if uu____15103
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm in
                       (let uu____15121 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck") in
                        if uu____15121
                        then
                          let uu____15122 =
                            FStar_Syntax_Print.uvar_to_string u in
                          let uu____15123 =
                            FStar_Syntax_Print.term_to_string tm1 in
                          let uu____15124 =
                            FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____15122 uu____15123 uu____15124
                        else ());
                       (let uu____15126 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___185_15130 = env1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___185_15130.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___185_15130.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___185_15130.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___185_15130.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___185_15130.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___185_15130.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___185_15130.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___185_15130.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___185_15130.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___185_15130.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___185_15130.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___185_15130.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___185_15130.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___185_15130.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___185_15130.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___185_15130.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___185_15130.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___185_15130.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___185_15130.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___185_15130.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___185_15130.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___185_15130.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___185_15130.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___185_15130.FStar_TypeChecker_Env.proof_ns)
                             }) tm1 in
                        match uu____15126 with
                        | (uu____15131,uu____15132,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___186_15135 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___186_15135.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___186_15135.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___186_15135.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____15138 =
                                discharge_guard'
                                  (Some
                                     (fun uu____15142  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____15138 with
                              | Some g3 -> g3
                              | None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
    let uu___187_15157 = g in
    let uu____15158 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___187_15157.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___187_15157.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___187_15157.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____15158
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____15186 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____15186 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15193 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15193
      | (reason,uu____15195,uu____15196,e,t,r)::uu____15200 ->
          let uu____15214 =
            let uu____15215 = FStar_Syntax_Print.term_to_string t in
            let uu____15216 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format3
              "Failed to resolve implicit argument of type '%s' introduced in %s because %s"
              uu____15215 uu____15216 reason in
          FStar_Errors.err r uu____15214
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___188_15223 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___188_15223.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___188_15223.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___188_15223.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15241 = try_teq false env t1 t2 in
        match uu____15241 with
        | None  -> false
        | Some g ->
            let uu____15244 = discharge_guard' None env g false in
            (match uu____15244 with
             | Some uu____15248 -> true
             | None  -> false)