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
  fun uu____976  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1026 = next_pid () in
  let uu____1027 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1026;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1027;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1074 = next_pid () in
  let uu____1075 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1074;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1075;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1116 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1116;
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
        let uu____1168 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1168
        then
          let uu____1169 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1170 = prob_to_string env d in
          let uu____1171 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1169 uu____1170 uu____1171 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1176 -> failwith "impossible" in
           let uu____1177 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1185 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1186 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1185, uu____1186)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1190 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1191 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1190, uu____1191) in
           match uu____1177 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___119_1200  ->
            match uu___119_1200 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1206 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1208),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___120_1221  ->
           match uu___120_1221 with
           | UNIV uu____1223 -> None
           | TERM ((u,uu____1227),t) ->
               let uu____1231 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1231 then Some t else None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___121_1243  ->
           match uu___121_1243 with
           | UNIV (u',t) ->
               let uu____1247 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1247 then Some t else None
           | uu____1250 -> None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1257 =
        let uu____1258 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1258 in
      FStar_Syntax_Subst.compress uu____1257
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1265 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1265
let norm_arg env t = let uu____1284 = sn env (fst t) in (uu____1284, (snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1301  ->
              match uu____1301 with
              | (x,imp) ->
                  let uu____1308 =
                    let uu___144_1309 = x in
                    let uu____1310 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___144_1309.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___144_1309.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1310
                    } in
                  (uu____1308, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1325 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1325
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1328 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1328
        | uu____1330 -> u2 in
      let uu____1331 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1331
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1438 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____1438 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1450;
               FStar_Syntax_Syntax.pos = uu____1451;
               FStar_Syntax_Syntax.vars = uu____1452;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1473 =
                 let uu____1474 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1475 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1474
                   uu____1475 in
               failwith uu____1473)
    | FStar_Syntax_Syntax.Tm_uinst uu____1485 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1512 =
             let uu____1513 = FStar_Syntax_Subst.compress t1' in
             uu____1513.FStar_Syntax_Syntax.n in
           match uu____1512 with
           | FStar_Syntax_Syntax.Tm_refine uu____1525 -> aux true t1'
           | uu____1530 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1542 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1565 =
             let uu____1566 = FStar_Syntax_Subst.compress t1' in
             uu____1566.FStar_Syntax_Syntax.n in
           match uu____1565 with
           | FStar_Syntax_Syntax.Tm_refine uu____1578 -> aux true t1'
           | uu____1583 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_app uu____1595 ->
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
    | FStar_Syntax_Syntax.Tm_type uu____1657 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_constant uu____1669 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_name uu____1681 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1693 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1705 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_abs uu____1724 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1750 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_let uu____1770 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_match uu____1789 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_meta uu____1816 ->
        let uu____1821 =
          let uu____1822 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1823 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1822
            uu____1823 in
        failwith uu____1821
    | FStar_Syntax_Syntax.Tm_ascribed uu____1833 ->
        let uu____1851 =
          let uu____1852 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1853 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1852
            uu____1853 in
        failwith uu____1851
    | FStar_Syntax_Syntax.Tm_delayed uu____1863 ->
        let uu____1884 =
          let uu____1885 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1886 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1885
            uu____1886 in
        failwith uu____1884
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1896 =
          let uu____1897 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1898 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1897
            uu____1898 in
        failwith uu____1896 in
  let uu____1908 = whnf env t1 in aux false uu____1908
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1917 =
        let uu____1927 = empty_worklist env in
        base_and_refinement env uu____1927 t in
      FStar_All.pipe_right uu____1917 FStar_Pervasives.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____1951 = FStar_Syntax_Syntax.null_bv t in
    (uu____1951, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____1971 = base_and_refinement env wl t in
  match uu____1971 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
let force_refinement uu____2030 =
  match uu____2030 with
  | (t_base,refopt) ->
      let uu____2044 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base in
      (match uu____2044 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___122_2068  ->
      match uu___122_2068 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2072 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2073 =
            let uu____2074 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____2074 in
          let uu____2075 =
            let uu____2076 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____2076 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2072 uu____2073
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2075
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2080 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2081 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____2082 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2080 uu____2081
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2082
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2086 =
      let uu____2088 =
        let uu____2090 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2100  ->
                  match uu____2100 with | (uu____2104,uu____2105,x) -> x)) in
        FStar_List.append wl.attempting uu____2090 in
      FStar_List.map (wl_prob_to_string wl) uu____2088 in
    FStar_All.pipe_right uu____2086 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2123 =
          let uu____2133 =
            let uu____2134 = FStar_Syntax_Subst.compress k in
            uu____2134.FStar_Syntax_Syntax.n in
          match uu____2133 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2179 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2179)
              else
                (let uu____2193 = FStar_Syntax_Util.abs_formals t in
                 match uu____2193 with
                 | (ys',t1,uu____2214) ->
                     let uu____2227 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2227))
          | uu____2248 ->
              let uu____2249 =
                let uu____2255 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____2255) in
              ((ys, t), uu____2249) in
        match uu____2123 with
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
                      ((let uu____2401 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2401
                        then
                          let uu____2402 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2403 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2404 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2402
                            uu____2403 uu____2404
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2406 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___145_2409 = wl in
                  {
                    attempting = (uu___145_2409.attempting);
                    wl_deferred = (uu___145_2409.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___145_2409.defer_ok);
                    smt_ok = (uu___145_2409.smt_ok);
                    tcenv = (uu___145_2409.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2422 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2422
         then
           let uu____2423 = FStar_Util.string_of_int pid in
           let uu____2424 =
             let uu____2425 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2425 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2423 uu____2424
         else ());
        commit sol;
        (let uu___146_2430 = wl in
         {
           attempting = (uu___146_2430.attempting);
           wl_deferred = (uu___146_2430.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___146_2430.defer_ok);
           smt_ok = (uu___146_2430.smt_ok);
           tcenv = (uu___146_2430.tcenv)
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
            | (uu____2459,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2467 = FStar_Syntax_Util.mk_conj t1 f in
                Some uu____2467 in
          (let uu____2473 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2473
           then
             let uu____2474 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2475 =
               let uu____2476 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2476 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2474 uu____2475
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2501 =
    let uu____2505 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2505 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2501
    (FStar_Util.for_some
       (fun uu____2522  ->
          match uu____2522 with
          | (uv,uu____2526) -> FStar_Syntax_Unionfind.equiv uv (fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2559 = occurs wl uk t in Prims.op_Negation uu____2559 in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2564 =
         let uu____2565 = FStar_Syntax_Print.uvar_to_string (fst uk) in
         let uu____2566 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2565 uu____2566 in
       Some uu____2564) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2614 = occurs_check env wl uk t in
  match uu____2614 with
  | (occurs_ok,msg) ->
      let uu____2631 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2631, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2695 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2719  ->
            fun uu____2720  ->
              match (uu____2719, uu____2720) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2763 =
                    let uu____2764 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2764 in
                  if uu____2763
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2778 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2778
                     then
                       let uu____2785 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____2785)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2695 with | (isect,uu____2807) -> FStar_List.rev isect
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
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3013;
           FStar_Syntax_Syntax.tk = uu____3014;
           FStar_Syntax_Syntax.pos = uu____3015;
           FStar_Syntax_Syntax.vars = uu____3016;_},uu____3017)
        -> true
    | uu____3040 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3102;
         FStar_Syntax_Syntax.pos = uu____3103;
         FStar_Syntax_Syntax.vars = uu____3104;_},args)
      -> (t, uv, k, args)
  | uu____3145 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____3199 = destruct_flex_t t in
  match uu____3199 with
  | (t1,uv,k,args) ->
      let uu____3267 = pat_vars env [] args in
      (match uu____3267 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3323 -> ((t1, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth option*
  FStar_Syntax_Syntax.delta_depth option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3371 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth option* FStar_Syntax_Syntax.delta_depth
      option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3394 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3398 -> false
let head_match: match_result -> match_result =
  fun uu___123_3401  ->
    match uu___123_3401 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3410 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3423 ->
          let uu____3424 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3424 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3434 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3448 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3454 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> None
      | FStar_Syntax_Syntax.Tm_bvar uu____3476 -> None
      | FStar_Syntax_Syntax.Tm_name uu____3477 -> None
      | FStar_Syntax_Syntax.Tm_uvar uu____3478 -> None
      | FStar_Syntax_Syntax.Tm_let uu____3487 -> None
      | FStar_Syntax_Syntax.Tm_match uu____3495 -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3512) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3518,uu____3519) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3549) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3564;
             FStar_Syntax_Syntax.index = uu____3565;
             FStar_Syntax_Syntax.sort = t2;_},uu____3567)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3574 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3575 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3576 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3584 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3600 = fv_delta_depth env fv in Some uu____3600
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
            let uu____3619 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3619
            then FullMatch
            else
              (let uu____3621 =
                 let uu____3626 =
                   let uu____3628 = fv_delta_depth env f in Some uu____3628 in
                 let uu____3629 =
                   let uu____3631 = fv_delta_depth env g in Some uu____3631 in
                 (uu____3626, uu____3629) in
               MisMatch uu____3621)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3635),FStar_Syntax_Syntax.Tm_uinst (g,uu____3637)) ->
            let uu____3646 = head_matches env f g in
            FStar_All.pipe_right uu____3646 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3653),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3655)) ->
            let uu____3680 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____3680 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3685),FStar_Syntax_Syntax.Tm_refine (y,uu____3687)) ->
            let uu____3696 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3696 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3698),uu____3699) ->
            let uu____3704 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3704 head_match
        | (uu____3705,FStar_Syntax_Syntax.Tm_refine (x,uu____3707)) ->
            let uu____3712 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3712 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3713,FStar_Syntax_Syntax.Tm_type
           uu____3714) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3715,FStar_Syntax_Syntax.Tm_arrow uu____3716) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3732),FStar_Syntax_Syntax.Tm_app (head',uu____3734))
            ->
            let uu____3763 = head_matches env head1 head' in
            FStar_All.pipe_right uu____3763 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3765),uu____3766) ->
            let uu____3781 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____3781 head_match
        | (uu____3782,FStar_Syntax_Syntax.Tm_app (head1,uu____3784)) ->
            let uu____3799 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____3799 head_match
        | uu____3800 ->
            let uu____3803 =
              let uu____3808 = delta_depth_of_term env t11 in
              let uu____3810 = delta_depth_of_term env t21 in
              (uu____3808, uu____3810) in
            MisMatch uu____3803
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3846 = FStar_Syntax_Util.head_and_args t in
    match uu____3846 with
    | (head1,uu____3858) ->
        let uu____3873 =
          let uu____3874 = FStar_Syntax_Util.un_uinst head1 in
          uu____3874.FStar_Syntax_Syntax.n in
        (match uu____3873 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3879 =
               let uu____3880 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____3880 FStar_Option.isSome in
             if uu____3879
             then
               let uu____3894 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____3894 (fun _0_38  -> Some _0_38)
             else None
         | uu____3897 -> None) in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None)) in
  let fail r = (r, None) in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21 in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),uu____3965) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____3975 =
             let uu____3980 = maybe_inline t11 in
             let uu____3982 = maybe_inline t21 in (uu____3980, uu____3982) in
           match uu____3975 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (uu____4003,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4013 =
             let uu____4018 = maybe_inline t11 in
             let uu____4020 = maybe_inline t21 in (uu____4018, uu____4020) in
           match uu____4013 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____4045 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____4045 with
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
        let uu____4060 =
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
             let uu____4068 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____4068)) in
        (match uu____4060 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4076 -> fail r
    | uu____4081 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4106 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4136 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4151 = FStar_Syntax_Util.type_u () in
      match uu____4151 with
      | (t,uu____4155) ->
          let uu____4156 = new_uvar r binders t in fst uu____4156
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4165 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____4165 FStar_Pervasives.fst
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
        let uu____4207 = head_matches env t1 t' in
        match uu____4207 with
        | MisMatch uu____4208 -> false
        | uu____4213 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4273,imp),T (t2,uu____4276)) -> (t2, imp)
                     | uu____4293 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4333  ->
                    match uu____4333 with
                    | (t2,uu____4341) ->
                        (None, INVARIANT, (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let fail uu____4374 = failwith "Bad reconstruction" in
          let uu____4375 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____4375 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4428))::tcs2) ->
                       aux
                         (((let uu___147_4450 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___147_4450.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___147_4450.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4460 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___124_4491 =
                 match uu___124_4491 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4554 = decompose1 [] bs1 in
               (rebuild, matches, uu____4554))
      | uu____4582 ->
          let rebuild uu___125_4587 =
            match uu___125_4587 with
            | [] -> t1
            | uu____4589 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___126_4608  ->
    match uu___126_4608 with
    | T (t,uu____4610) -> t
    | uu____4619 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___127_4622  ->
    match uu___127_4622 with
    | T (t,uu____4624) -> FStar_Syntax_Syntax.as_arg t
    | uu____4633 -> failwith "Impossible"
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
              | (uu____4702,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4721 = new_uvar r scope1 k in
                  (match uu____4721 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4733 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args)) None r in
                       let uu____4748 =
                         let uu____4749 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_39  ->
                              FStar_TypeChecker_Common.TProb _0_39)
                           uu____4749 in
                       ((T (gi_xs, mk_kind)), uu____4748))
              | (uu____4758,uu____4759,C uu____4760) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4847 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4858;
                         FStar_Syntax_Syntax.pos = uu____4859;
                         FStar_Syntax_Syntax.vars = uu____4860;_})
                        ->
                        let uu____4875 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4875 with
                         | (T (gi_xs,uu____4891),prob) ->
                             let uu____4901 =
                               let uu____4902 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_40  -> C _0_40)
                                 uu____4902 in
                             (uu____4901, [prob])
                         | uu____4904 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4914;
                         FStar_Syntax_Syntax.pos = uu____4915;
                         FStar_Syntax_Syntax.vars = uu____4916;_})
                        ->
                        let uu____4931 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4931 with
                         | (T (gi_xs,uu____4947),prob) ->
                             let uu____4957 =
                               let uu____4958 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_41  -> C _0_41)
                                 uu____4958 in
                             (uu____4957, [prob])
                         | uu____4960 -> failwith "impossible")
                    | (uu____4966,uu____4967,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____4969;
                         FStar_Syntax_Syntax.pos = uu____4970;
                         FStar_Syntax_Syntax.vars = uu____4971;_})
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
                        let uu____5045 =
                          let uu____5050 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____5050 FStar_List.unzip in
                        (match uu____5045 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5079 =
                                 let uu____5080 =
                                   let uu____5083 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____5083 un_T in
                                 let uu____5084 =
                                   let uu____5090 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____5090
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5080;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5084;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5079 in
                             ((C gi_xs), sub_probs))
                    | uu____5095 ->
                        let uu____5102 = sub_prob scope1 args q in
                        (match uu____5102 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____4847 with
                   | (tc,probs) ->
                       let uu____5120 =
                         match q with
                         | (Some b,uu____5146,uu____5147) ->
                             let uu____5155 =
                               let uu____5159 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____5159 :: args in
                             ((Some b), (b :: scope1), uu____5155)
                         | uu____5177 -> (None, scope1, args) in
                       (match uu____5120 with
                        | (bopt,scope2,args1) ->
                            let uu____5220 = aux scope2 args1 qs2 in
                            (match uu____5220 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____5241 =
                                         let uu____5243 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         f :: uu____5243 in
                                       FStar_Syntax_Util.mk_conj_l uu____5241
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (fst b).FStar_Syntax_Syntax.sort in
                                       let uu____5256 =
                                         let uu____5258 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (fst b) f in
                                         let uu____5259 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         uu____5258 :: uu____5259 in
                                       FStar_Syntax_Util.mk_conj_l uu____5256 in
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
  let uu___148_5312 = p in
  let uu____5315 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____5316 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___148_5312.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5315;
    FStar_TypeChecker_Common.relation =
      (uu___148_5312.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5316;
    FStar_TypeChecker_Common.element =
      (uu___148_5312.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___148_5312.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___148_5312.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___148_5312.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___148_5312.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___148_5312.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5326 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____5326
            (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
      | FStar_TypeChecker_Common.CProb uu____5331 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5345 = compress_prob wl pr in
        FStar_All.pipe_right uu____5345 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5351 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____5351 with
           | (lh,uu____5364) ->
               let uu____5379 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____5379 with
                | (rh,uu____5392) ->
                    let uu____5407 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5416,FStar_Syntax_Syntax.Tm_uvar uu____5417)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5436,uu____5437)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5448,FStar_Syntax_Syntax.Tm_uvar uu____5449)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5460,uu____5461)
                          ->
                          let uu____5470 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5470 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5510 ->
                                    let rank =
                                      let uu____5517 = is_top_level_prob prob in
                                      if uu____5517
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5519 =
                                      let uu___149_5522 = tp in
                                      let uu____5525 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_5522.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___149_5522.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_5522.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5525;
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_5522.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_5522.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_5522.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_5522.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_5522.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_5522.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5519)))
                      | (uu____5535,FStar_Syntax_Syntax.Tm_uvar uu____5536)
                          ->
                          let uu____5545 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5545 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5585 ->
                                    let uu____5591 =
                                      let uu___150_5596 = tp in
                                      let uu____5599 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___150_5596.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5599;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___150_5596.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___150_5596.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___150_5596.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___150_5596.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___150_5596.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___150_5596.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___150_5596.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___150_5596.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5591)))
                      | (uu____5615,uu____5616) -> (rigid_rigid, tp) in
                    (match uu____5407 with
                     | (rank,tp1) ->
                         let uu____5627 =
                           FStar_All.pipe_right
                             (let uu___151_5630 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___151_5630.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___151_5630.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___151_5630.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___151_5630.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___151_5630.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___151_5630.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___151_5630.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___151_5630.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___151_5630.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_43  ->
                                FStar_TypeChecker_Common.TProb _0_43) in
                         (rank, uu____5627))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5636 =
            FStar_All.pipe_right
              (let uu___152_5639 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___152_5639.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___152_5639.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___152_5639.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___152_5639.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___152_5639.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___152_5639.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___152_5639.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___152_5639.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___152_5639.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) in
          (rigid_rigid, uu____5636)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob option* FStar_TypeChecker_Common.prob
      Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____5671 probs =
      match uu____5671 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5701 = rank wl hd1 in
               (match uu____5701 with
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
    match projectee with | UDeferred _0 -> true | uu____5766 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5778 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5790 -> false
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
                        let uu____5823 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____5823 with
                        | (k,uu____5827) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____5831 -> false)))
            | uu____5832 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____5879 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____5879 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5882 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____5888 =
                     let uu____5889 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____5890 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5889
                       uu____5890 in
                   UFailed uu____5888)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5906 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5906 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5924 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5924 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____5927 ->
                let uu____5930 =
                  let uu____5931 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____5932 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5931
                    uu____5932 msg in
                UFailed uu____5930 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____5933,uu____5934) ->
              let uu____5935 =
                let uu____5936 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5937 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5936 uu____5937 in
              failwith uu____5935
          | (FStar_Syntax_Syntax.U_unknown ,uu____5938) ->
              let uu____5939 =
                let uu____5940 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5941 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5940 uu____5941 in
              failwith uu____5939
          | (uu____5942,FStar_Syntax_Syntax.U_bvar uu____5943) ->
              let uu____5944 =
                let uu____5945 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5946 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5945 uu____5946 in
              failwith uu____5944
          | (uu____5947,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____5948 =
                let uu____5949 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5950 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5949 uu____5950 in
              failwith uu____5948
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____5962 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____5962
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____5972 = occurs_univ v1 u3 in
              if uu____5972
              then
                let uu____5973 =
                  let uu____5974 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____5975 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5974 uu____5975 in
                try_umax_components u11 u21 uu____5973
              else
                (let uu____5977 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____5977)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____5985 = occurs_univ v1 u3 in
              if uu____5985
              then
                let uu____5986 =
                  let uu____5987 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____5988 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5987 uu____5988 in
                try_umax_components u11 u21 uu____5986
              else
                (let uu____5990 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____5990)
          | (FStar_Syntax_Syntax.U_max uu____5993,uu____5994) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____5999 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____5999
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____6001,FStar_Syntax_Syntax.U_max uu____6002) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6007 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6007
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6009,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6010,FStar_Syntax_Syntax.U_name
             uu____6011) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6012) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6013) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6014,FStar_Syntax_Syntax.U_succ
             uu____6015) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6016,FStar_Syntax_Syntax.U_zero
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
  let uu____6078 = bc1 in
  match uu____6078 with
  | (bs1,mk_cod1) ->
      let uu____6103 = bc2 in
      (match uu____6103 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6150 = FStar_Util.first_N n1 bs in
             match uu____6150 with
             | (bs3,rest) ->
                 let uu____6164 = mk_cod rest in (bs3, uu____6164) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____6188 =
               let uu____6192 = mk_cod1 [] in (bs1, uu____6192) in
             let uu____6194 =
               let uu____6198 = mk_cod2 [] in (bs2, uu____6198) in
             (uu____6188, uu____6194)
           else
             if l1 > l2
             then
               (let uu____6225 = curry l2 bs1 mk_cod1 in
                let uu____6235 =
                  let uu____6239 = mk_cod2 [] in (bs2, uu____6239) in
                (uu____6225, uu____6235))
             else
               (let uu____6248 =
                  let uu____6252 = mk_cod1 [] in (bs1, uu____6252) in
                let uu____6254 = curry l1 bs2 mk_cod2 in
                (uu____6248, uu____6254)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6361 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____6361
       then
         let uu____6362 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6362
       else ());
      (let uu____6364 = next_prob probs in
       match uu____6364 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___153_6377 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___153_6377.wl_deferred);
               ctr = (uu___153_6377.ctr);
               defer_ok = (uu___153_6377.defer_ok);
               smt_ok = (uu___153_6377.smt_ok);
               tcenv = (uu___153_6377.tcenv)
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
                  let uu____6384 = solve_flex_rigid_join env tp probs1 in
                  (match uu____6384 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6388 = solve_rigid_flex_meet env tp probs1 in
                     match uu____6388 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____6392,uu____6393) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6402 ->
                let uu____6407 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6435  ->
                          match uu____6435 with
                          | (c,uu____6440,uu____6441) -> c < probs.ctr)) in
                (match uu____6407 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6463 =
                            FStar_List.map
                              (fun uu____6469  ->
                                 match uu____6469 with
                                 | (uu____6475,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____6463
                      | uu____6478 ->
                          let uu____6483 =
                            let uu___154_6484 = probs in
                            let uu____6485 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6494  ->
                                      match uu____6494 with
                                      | (uu____6498,uu____6499,y) -> y)) in
                            {
                              attempting = uu____6485;
                              wl_deferred = rest;
                              ctr = (uu___154_6484.ctr);
                              defer_ok = (uu___154_6484.defer_ok);
                              smt_ok = (uu___154_6484.smt_ok);
                              tcenv = (uu___154_6484.tcenv)
                            } in
                          solve env uu____6483))))
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
            let uu____6506 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____6506 with
            | USolved wl1 ->
                let uu____6508 = solve_prob orig None [] wl1 in
                solve env uu____6508
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
                  let uu____6542 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6542 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6545 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6553;
                  FStar_Syntax_Syntax.pos = uu____6554;
                  FStar_Syntax_Syntax.vars = uu____6555;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6558;
                  FStar_Syntax_Syntax.pos = uu____6559;
                  FStar_Syntax_Syntax.vars = uu____6560;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6572,uu____6573) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6578,FStar_Syntax_Syntax.Tm_uinst uu____6579) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6584 -> USolved wl
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
            ((let uu____6592 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6592
              then
                let uu____6593 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6593 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6601 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6601
         then
           let uu____6602 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6602
         else ());
        (let uu____6604 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6604 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6646 = head_matches_delta env () t1 t2 in
               match uu____6646 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6668 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6694 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6703 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____6704 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____6703, uu____6704)
                          | None  ->
                              let uu____6707 = FStar_Syntax_Subst.compress t1 in
                              let uu____6708 = FStar_Syntax_Subst.compress t2 in
                              (uu____6707, uu____6708) in
                        (match uu____6694 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6730 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_45  ->
                                    FStar_TypeChecker_Common.TProb _0_45)
                                 uu____6730 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6753 =
                                    let uu____6759 =
                                      let uu____6762 =
                                        let uu____6765 =
                                          let uu____6766 =
                                            let uu____6771 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____6771) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6766 in
                                        FStar_Syntax_Syntax.mk uu____6765 in
                                      uu____6762 None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____6784 =
                                      let uu____6786 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____6786] in
                                    (uu____6759, uu____6784) in
                                  Some uu____6753
                              | (uu____6795,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6797)) ->
                                  let uu____6802 =
                                    let uu____6806 =
                                      let uu____6808 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____6808] in
                                    (t11, uu____6806) in
                                  Some uu____6802
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6814),uu____6815) ->
                                  let uu____6820 =
                                    let uu____6824 =
                                      let uu____6826 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____6826] in
                                    (t21, uu____6824) in
                                  Some uu____6820
                              | uu____6831 ->
                                  let uu____6834 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____6834 with
                                   | (head1,uu____6849) ->
                                       let uu____6864 =
                                         let uu____6865 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____6865.FStar_Syntax_Syntax.n in
                                       (match uu____6864 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6872;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6874;_}
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
                                        | uu____6883 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6892) ->
                  let uu____6905 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___128_6914  ->
                            match uu___128_6914 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6919 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____6919 with
                                      | (u',uu____6930) ->
                                          let uu____6945 =
                                            let uu____6946 = whnf env u' in
                                            uu____6946.FStar_Syntax_Syntax.n in
                                          (match uu____6945 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____6950) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____6963 -> false))
                                 | uu____6964 -> false)
                            | uu____6966 -> false)) in
                  (match uu____6905 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____6987 tps =
                         match uu____6987 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7014 =
                                    let uu____7019 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____7019 in
                                  (match uu____7014 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____7038 -> None) in
                       let uu____7043 =
                         let uu____7048 =
                           let uu____7052 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____7052, []) in
                         make_lower_bound uu____7048 lower_bounds in
                       (match uu____7043 with
                        | None  ->
                            ((let uu____7059 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7059
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
                            ((let uu____7072 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7072
                              then
                                let wl' =
                                  let uu___155_7074 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___155_7074.wl_deferred);
                                    ctr = (uu___155_7074.ctr);
                                    defer_ok = (uu___155_7074.defer_ok);
                                    smt_ok = (uu___155_7074.smt_ok);
                                    tcenv = (uu___155_7074.tcenv)
                                  } in
                                let uu____7075 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7075
                              else ());
                             (let uu____7077 =
                                solve_t env eq_prob
                                  (let uu___156_7078 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___156_7078.wl_deferred);
                                     ctr = (uu___156_7078.ctr);
                                     defer_ok = (uu___156_7078.defer_ok);
                                     smt_ok = (uu___156_7078.smt_ok);
                                     tcenv = (uu___156_7078.tcenv)
                                   }) in
                              match uu____7077 with
                              | Success uu____7080 ->
                                  let wl1 =
                                    let uu___157_7082 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___157_7082.wl_deferred);
                                      ctr = (uu___157_7082.ctr);
                                      defer_ok = (uu___157_7082.defer_ok);
                                      smt_ok = (uu___157_7082.smt_ok);
                                      tcenv = (uu___157_7082.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1 in
                                  let uu____7084 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds in
                                  Some wl2
                              | uu____7087 -> None))))
              | uu____7088 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7095 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____7095
         then
           let uu____7096 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7096
         else ());
        (let uu____7098 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____7098 with
         | (u,args) ->
             let uu____7125 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____7125 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____7156 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____7156 with
                    | (h1,args1) ->
                        let uu____7184 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____7184 with
                         | (h2,uu____7197) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7216 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____7216
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7231 =
                                          let uu____7233 =
                                            let uu____7234 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_46  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_46) uu____7234 in
                                          [uu____7233] in
                                        Some uu____7231))
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
                                       (let uu____7258 =
                                          let uu____7260 =
                                            let uu____7261 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_47  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_47) uu____7261 in
                                          [uu____7260] in
                                        Some uu____7258))
                                  else None
                              | uu____7269 -> None)) in
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
                             let uu____7335 =
                               let uu____7341 =
                                 let uu____7344 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____7344 in
                               (uu____7341, m1) in
                             Some uu____7335)
                    | (uu____7353,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7355)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7387),uu____7388) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____7419 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7453) ->
                       let uu____7466 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___129_7475  ->
                                 match uu___129_7475 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____7480 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____7480 with
                                           | (u',uu____7491) ->
                                               let uu____7506 =
                                                 let uu____7507 = whnf env u' in
                                                 uu____7507.FStar_Syntax_Syntax.n in
                                               (match uu____7506 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7511) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____7524 -> false))
                                      | uu____7525 -> false)
                                 | uu____7527 -> false)) in
                       (match uu____7466 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7552 tps =
                              match uu____7552 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7593 =
                                         let uu____7600 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7600 in
                                       (match uu____7593 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7635 -> None) in
                            let uu____7642 =
                              let uu____7649 =
                                let uu____7655 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7655, []) in
                              make_upper_bound uu____7649 upper_bounds in
                            (match uu____7642 with
                             | None  ->
                                 ((let uu____7664 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7664
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
                                 ((let uu____7683 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7683
                                   then
                                     let wl' =
                                       let uu___158_7685 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___158_7685.wl_deferred);
                                         ctr = (uu___158_7685.ctr);
                                         defer_ok = (uu___158_7685.defer_ok);
                                         smt_ok = (uu___158_7685.smt_ok);
                                         tcenv = (uu___158_7685.tcenv)
                                       } in
                                     let uu____7686 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7686
                                   else ());
                                  (let uu____7688 =
                                     solve_t env eq_prob
                                       (let uu___159_7689 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___159_7689.wl_deferred);
                                          ctr = (uu___159_7689.ctr);
                                          defer_ok = (uu___159_7689.defer_ok);
                                          smt_ok = (uu___159_7689.smt_ok);
                                          tcenv = (uu___159_7689.tcenv)
                                        }) in
                                   match uu____7688 with
                                   | Success uu____7691 ->
                                       let wl1 =
                                         let uu___160_7693 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___160_7693.wl_deferred);
                                           ctr = (uu___160_7693.ctr);
                                           defer_ok =
                                             (uu___160_7693.defer_ok);
                                           smt_ok = (uu___160_7693.smt_ok);
                                           tcenv = (uu___160_7693.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1 in
                                       let uu____7695 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds in
                                       Some wl2
                                   | uu____7698 -> None))))
                   | uu____7699 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____7764 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____7764
                      then
                        let uu____7765 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7765
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___161_7797 = hd1 in
                      let uu____7798 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_7797.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_7797.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7798
                      } in
                    let hd21 =
                      let uu___162_7802 = hd2 in
                      let uu____7803 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___162_7802.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___162_7802.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7803
                      } in
                    let prob =
                      let uu____7807 =
                        let uu____7810 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7810 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_48  -> FStar_TypeChecker_Common.TProb _0_48)
                        uu____7807 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____7818 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7818 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____7821 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____7821 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7839 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives.fst in
                           let uu____7842 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____7839 uu____7842 in
                         ((let uu____7848 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____7848
                           then
                             let uu____7849 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____7850 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7849 uu____7850
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7865 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____7871 = aux scope env [] bs1 bs2 in
              match uu____7871 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7887 = compress_tprob wl problem in
        solve_t' env uu____7887 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7920 = head_matches_delta env1 wl1 t1 t2 in
          match uu____7920 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7937,uu____7938) ->
                   let may_relate head3 =
                     let uu____7953 =
                       let uu____7954 = FStar_Syntax_Util.un_uinst head3 in
                       uu____7954.FStar_Syntax_Syntax.n in
                     match uu____7953 with
                     | FStar_Syntax_Syntax.Tm_name uu____7957 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____7958 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____7975 -> false in
                   let uu____7976 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____7976
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
                                let uu____7993 =
                                  let uu____7994 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____7994 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____7993 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____7996 = solve_prob orig (Some guard) [] wl1 in
                     solve env1 uu____7996
                   else
                     (let uu____7998 =
                        let uu____7999 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____8000 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____7999 uu____8000 in
                      giveup env1 uu____7998 orig)
               | (uu____8001,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___163_8009 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___163_8009.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___163_8009.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___163_8009.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___163_8009.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___163_8009.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___163_8009.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___163_8009.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___163_8009.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____8010,None ) ->
                   ((let uu____8017 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8017
                     then
                       let uu____8018 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____8019 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____8020 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____8021 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____8018
                         uu____8019 uu____8020 uu____8021
                     else ());
                    (let uu____8023 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____8023 with
                     | (head11,args1) ->
                         let uu____8049 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____8049 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8094 =
                                  let uu____8095 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____8096 = args_to_string args1 in
                                  let uu____8097 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____8098 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8095 uu____8096 uu____8097
                                    uu____8098 in
                                giveup env1 uu____8094 orig
                              else
                                (let uu____8100 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8105 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____8105 = FStar_Syntax_Util.Equal) in
                                 if uu____8100
                                 then
                                   let uu____8106 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____8106 with
                                   | USolved wl2 ->
                                       let uu____8108 =
                                         solve_prob orig None [] wl2 in
                                       solve env1 uu____8108
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8112 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____8112 with
                                    | (base1,refinement1) ->
                                        let uu____8138 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____8138 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____8192 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____8192 with
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
                                                           (fun uu____8202 
                                                              ->
                                                              fun uu____8203 
                                                                ->
                                                                match 
                                                                  (uu____8202,
                                                                    uu____8203)
                                                                with
                                                                | ((a,uu____8213),
                                                                   (a',uu____8215))
                                                                    ->
                                                                    let uu____8220
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
                                                                    uu____8220)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____8226 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8226 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8230 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___164_8263 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___164_8263.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___164_8263.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___164_8263.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___164_8263.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___164_8263.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___164_8263.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___164_8263.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___164_8263.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____8283 = p in
          match uu____8283 with
          | (((u,k),xs,c),ps,(h,uu____8294,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8343 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____8343 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8357 = h gs_xs in
                     let uu____8358 =
                       let uu____8365 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_50  -> FStar_Util.Inl _0_50) in
                       FStar_All.pipe_right uu____8365
                         (fun _0_51  -> Some _0_51) in
                     FStar_Syntax_Util.abs xs1 uu____8357 uu____8358 in
                   ((let uu____8396 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8396
                     then
                       let uu____8397 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____8398 = FStar_Syntax_Print.comp_to_string c in
                       let uu____8399 = FStar_Syntax_Print.term_to_string im in
                       let uu____8400 = FStar_Syntax_Print.tag_of_term im in
                       let uu____8401 =
                         let uu____8402 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____8402
                           (FStar_String.concat ", ") in
                       let uu____8405 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8397 uu____8398 uu____8399 uu____8400
                         uu____8401 uu____8405
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___130_8423 =
          match uu___130_8423 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____8452 = p in
          match uu____8452 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8510 = FStar_List.nth ps i in
              (match uu____8510 with
               | (pi,uu____8513) ->
                   let uu____8518 = FStar_List.nth xs i in
                   (match uu____8518 with
                    | (xi,uu____8525) ->
                        let rec gs k =
                          let uu____8534 = FStar_Syntax_Util.arrow_formals k in
                          match uu____8534 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8586)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8594 = new_uvar r xs k_a in
                                    (match uu____8594 with
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
                                         let uu____8613 = aux subst2 tl1 in
                                         (match uu____8613 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8628 =
                                                let uu____8630 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8630 :: gi_xs' in
                                              let uu____8631 =
                                                let uu____8633 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8633 :: gi_ps' in
                                              (uu____8628, uu____8631))) in
                              aux [] bs in
                        let uu____8636 =
                          let uu____8637 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8637 in
                        if uu____8636
                        then None
                        else
                          (let uu____8640 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8640 with
                           | (g_xs,uu____8647) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8654 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r in
                                 let uu____8659 =
                                   let uu____8666 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_52  -> FStar_Util.Inl _0_52) in
                                   FStar_All.pipe_right uu____8666
                                     (fun _0_53  -> Some _0_53) in
                                 FStar_Syntax_Util.abs xs uu____8654
                                   uu____8659 in
                               let sub1 =
                                 let uu____8697 =
                                   let uu____8700 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let uu____8707 =
                                     let uu____8710 =
                                       FStar_List.map
                                         (fun uu____8716  ->
                                            match uu____8716 with
                                            | (uu____8721,uu____8722,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____8710 in
                                   mk_problem (p_scope orig) orig uu____8700
                                     (p_rel orig) uu____8707 None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_54  ->
                                      FStar_TypeChecker_Common.TProb _0_54)
                                   uu____8697 in
                               ((let uu____8732 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____8732
                                 then
                                   let uu____8733 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____8734 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8733 uu____8734
                                 else ());
                                (let wl2 =
                                   let uu____8737 =
                                     let uu____8739 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives.fst (p_guard sub1) in
                                     Some uu____8739 in
                                   solve_prob orig uu____8737
                                     [TERM (u, proj)] wl1 in
                                 let uu____8744 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_55  -> Some _0_55) uu____8744))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8768 = lhs in
          match uu____8768 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8791 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____8791 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8817 =
                        let uu____8843 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____8843) in
                      Some uu____8817
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____8926 =
                           let uu____8930 =
                             let uu____8931 = FStar_Syntax_Subst.compress k in
                             uu____8931.FStar_Syntax_Syntax.n in
                           (uu____8930, args) in
                         match uu____8926 with
                         | (uu____8938,[]) ->
                             let uu____8940 =
                               let uu____8946 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____8946) in
                             Some uu____8940
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____8957,uu____8958) ->
                             let uu____8969 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____8969 with
                              | (uv1,uv_args) ->
                                  let uu____8998 =
                                    let uu____8999 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____8999.FStar_Syntax_Syntax.n in
                                  (match uu____8998 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9006) ->
                                       let uu____9019 =
                                         pat_vars env [] uv_args in
                                       (match uu____9019 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9033  ->
                                                      let uu____9034 =
                                                        let uu____9035 =
                                                          let uu____9036 =
                                                            let uu____9039 =
                                                              let uu____9040
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9040
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9039 in
                                                          fst uu____9036 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9035 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9034)) in
                                            let c1 =
                                              let uu____9046 =
                                                let uu____9047 =
                                                  let uu____9050 =
                                                    let uu____9051 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9051
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9050 in
                                                fst uu____9047 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9046 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9060 =
                                                let uu____9067 =
                                                  let uu____9073 =
                                                    let uu____9074 =
                                                      let uu____9077 =
                                                        let uu____9078 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9078
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9077 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9074 in
                                                  FStar_Util.Inl uu____9073 in
                                                Some uu____9067 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9060 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9098 -> None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9101,uu____9102)
                             ->
                             let uu____9114 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9114 with
                              | (uv1,uv_args) ->
                                  let uu____9143 =
                                    let uu____9144 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9144.FStar_Syntax_Syntax.n in
                                  (match uu____9143 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9151) ->
                                       let uu____9164 =
                                         pat_vars env [] uv_args in
                                       (match uu____9164 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9178  ->
                                                      let uu____9179 =
                                                        let uu____9180 =
                                                          let uu____9181 =
                                                            let uu____9184 =
                                                              let uu____9185
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9185
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9184 in
                                                          fst uu____9181 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9180 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9179)) in
                                            let c1 =
                                              let uu____9191 =
                                                let uu____9192 =
                                                  let uu____9195 =
                                                    let uu____9196 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9196
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9195 in
                                                fst uu____9192 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9191 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9205 =
                                                let uu____9212 =
                                                  let uu____9218 =
                                                    let uu____9219 =
                                                      let uu____9222 =
                                                        let uu____9223 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9223
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9222 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9219 in
                                                  FStar_Util.Inl uu____9218 in
                                                Some uu____9212 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9205 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9243 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9248)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____9280 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____9280
                                 (fun _0_56  -> Some _0_56)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9304 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____9304 with
                                  | (args1,rest) ->
                                      let uu____9322 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____9322 with
                                       | (xs2,c2) ->
                                           let uu____9330 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____9330
                                             (fun uu____9341  ->
                                                match uu____9341 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9363 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____9363 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____9411 =
                                        let uu____9414 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9414 in
                                      FStar_All.pipe_right uu____9411
                                        (fun _0_57  -> Some _0_57))
                         | uu____9422 ->
                             let uu____9426 =
                               let uu____9427 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____9428 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____9429 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9427 uu____9428 uu____9429 in
                             failwith uu____9426 in
                       let uu____9433 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____9433
                         (fun uu____9461  ->
                            match uu____9461 with
                            | (xs1,c1) ->
                                let uu____9489 =
                                  let uu____9512 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9512) in
                                Some uu____9489)) in
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
                     let uu____9584 = imitate orig env wl1 st in
                     match uu____9584 with
                     | Failed uu____9589 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9595 = project orig env wl1 i st in
                      match uu____9595 with
                      | None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some (Failed uu____9602) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____9616 = FStar_Syntax_Util.head_and_args t21 in
                match uu____9616 with
                | (hd1,uu____9627) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9642 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9650 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9651 -> true
                     | uu____9666 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____9669 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____9669
                         then true
                         else
                           ((let uu____9672 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____9672
                             then
                               let uu____9673 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9673
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9681 =
                    let uu____9684 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____9684 FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____9681 FStar_Syntax_Free.names in
                let uu____9715 = FStar_Util.set_is_empty fvs_hd in
                if uu____9715
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____9724 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____9724 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9732 =
                            let uu____9733 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____9733 in
                          giveup_or_defer1 orig uu____9732
                        else
                          (let uu____9735 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____9735
                           then
                             let uu____9736 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____9736
                              then
                                let uu____9737 = subterms args_lhs in
                                imitate' orig env wl1 uu____9737
                              else
                                ((let uu____9741 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____9741
                                  then
                                    let uu____9742 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____9743 = names_to_string fvs1 in
                                    let uu____9744 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9742 uu____9743 uu____9744
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9749 ->
                                        let uu____9750 = sn_binders env vars in
                                        u_abs k_uv uu____9750 t21 in
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
                               (let uu____9759 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____9759
                                then
                                  ((let uu____9761 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____9761
                                    then
                                      let uu____9762 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____9763 = names_to_string fvs1 in
                                      let uu____9764 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9762 uu____9763 uu____9764
                                    else ());
                                   (let uu____9766 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9766
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
                     (let uu____9780 =
                        let uu____9781 = FStar_Syntax_Free.names t1 in
                        check_head uu____9781 t2 in
                      if uu____9780
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____9785 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____9785
                          then
                            let uu____9786 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9786
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9789 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9789 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9834 =
               match uu____9834 with
               | (t,u,k,args) ->
                   let uu____9864 = FStar_Syntax_Util.arrow_formals k in
                   (match uu____9864 with
                    | (all_formals,uu____9875) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____9967  ->
                                        match uu____9967 with
                                        | (x,imp) ->
                                            let uu____9974 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____9974, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____9982 = FStar_Syntax_Util.type_u () in
                                match uu____9982 with
                                | (t1,uu____9986) ->
                                    let uu____9987 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    fst uu____9987 in
                              let uu____9990 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____9990 with
                               | (t',tm_u1) ->
                                   let uu____9997 = destruct_flex_t t' in
                                   (match uu____9997 with
                                    | (uu____10017,u1,k1,uu____10020) ->
                                        let sol =
                                          let uu____10048 =
                                            let uu____10053 =
                                              u_abs k all_formals t' in
                                            ((u, k), uu____10053) in
                                          TERM uu____10048 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k1, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10113 = pat_var_opt env pat_args hd1 in
                              (match uu____10113 with
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
                                              (fun uu____10142  ->
                                                 match uu____10142 with
                                                 | (x,uu____10146) ->
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
                                      let uu____10152 =
                                        let uu____10153 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____10153 in
                                      if uu____10152
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10157 =
                                           FStar_Util.set_add (fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10157 formals1
                                           tl1)))
                          | uu____10163 -> failwith "Impossible" in
                        let uu____10174 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____10174 all_formals args) in
             let solve_both_pats wl1 uu____10214 uu____10215 r =
               match (uu____10214, uu____10215) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10329 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____10329
                   then
                     let uu____10330 = solve_prob orig None [] wl1 in
                     solve env uu____10330
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____10345 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____10345
                       then
                         let uu____10346 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____10347 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____10348 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____10349 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____10350 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10346 uu____10347 uu____10348 uu____10349
                           uu____10350
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____10398 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____10398 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10411 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____10411 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10443 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10443 in
                                  let uu____10446 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____10446 k3)
                           else
                             (let uu____10449 =
                                let uu____10450 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____10451 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____10452 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10450 uu____10451 uu____10452 in
                              failwith uu____10449) in
                       let uu____10453 =
                         let uu____10459 =
                           let uu____10467 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____10467 in
                         match uu____10459 with
                         | (bs,k1') ->
                             let uu____10485 =
                               let uu____10493 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____10493 in
                             (match uu____10485 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____10514 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_58  ->
                                         FStar_TypeChecker_Common.TProb _0_58)
                                      uu____10514 in
                                  let uu____10519 =
                                    let uu____10522 =
                                      let uu____10523 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____10523.FStar_Syntax_Syntax.n in
                                    let uu____10526 =
                                      let uu____10527 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____10527.FStar_Syntax_Syntax.n in
                                    (uu____10522, uu____10526) in
                                  (match uu____10519 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10535,uu____10536) ->
                                       (k1', [sub_prob])
                                   | (uu____10540,FStar_Syntax_Syntax.Tm_type
                                      uu____10541) -> (k2', [sub_prob])
                                   | uu____10545 ->
                                       let uu____10548 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____10548 with
                                        | (t,uu____10557) ->
                                            let uu____10558 = new_uvar r zs t in
                                            (match uu____10558 with
                                             | (k_zs,uu____10567) ->
                                                 let kprob =
                                                   let uu____10569 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_59  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_59) uu____10569 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____10453 with
                       | (k_u',sub_probs) ->
                           let uu____10583 =
                             let uu____10591 =
                               let uu____10592 = new_uvar r zs k_u' in
                               FStar_All.pipe_left FStar_Pervasives.fst
                                 uu____10592 in
                             let uu____10597 =
                               let uu____10600 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____10600 in
                             let uu____10603 =
                               let uu____10606 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____10606 in
                             (uu____10591, uu____10597, uu____10603) in
                           (match uu____10583 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____10625 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____10625 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____10637 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____10637
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____10641 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____10641 with
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
             let solve_one_pat uu____10673 uu____10674 =
               match (uu____10673, uu____10674) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10738 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____10738
                     then
                       let uu____10739 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10740 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10739 uu____10740
                     else ());
                    (let uu____10742 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____10742
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10749  ->
                              fun uu____10750  ->
                                match (uu____10749, uu____10750) with
                                | ((a,uu____10760),(t21,uu____10762)) ->
                                    let uu____10767 =
                                      let uu____10770 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____10770
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____10767
                                      (fun _0_60  ->
                                         FStar_TypeChecker_Common.TProb _0_60))
                           xs args2 in
                       let guard =
                         let uu____10774 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____10774 in
                       let wl1 = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____10784 = occurs_check env wl (u1, k1) t21 in
                        match uu____10784 with
                        | (occurs_ok,uu____10789) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____10794 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____10794
                            then
                              let sol =
                                let uu____10796 =
                                  let uu____10801 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____10801) in
                                TERM uu____10796 in
                              let wl1 = solve_prob orig None [sol] wl in
                              solve env wl1
                            else
                              (let uu____10806 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____10806
                               then
                                 let uu____10807 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____10807 with
                                 | (sol,(uu____10817,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____10827 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____10827
                                       then
                                         let uu____10828 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10828
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10833 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____10835 = lhs in
             match uu____10835 with
             | (t1,u1,k1,args1) ->
                 let uu____10840 = rhs in
                 (match uu____10840 with
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
                       | uu____10866 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____10872 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____10872 with
                              | (sol,uu____10879) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____10882 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____10882
                                    then
                                      let uu____10883 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____10883
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____10888 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____10890 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____10890
        then
          let uu____10891 = solve_prob orig None [] wl in
          solve env uu____10891
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____10895 = FStar_Util.physical_equality t1 t2 in
           if uu____10895
           then
             let uu____10896 = solve_prob orig None [] wl in
             solve env uu____10896
           else
             ((let uu____10899 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____10899
               then
                 let uu____10900 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____10900
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____10903,uu____10904) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____10905,FStar_Syntax_Syntax.Tm_bvar uu____10906) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___131_10946 =
                     match uu___131_10946 with
                     | [] -> c
                     | bs ->
                         let uu____10960 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c)) None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____10960 in
                   let uu____10970 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____10970 with
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
                                   let uu____11056 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____11056
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____11058 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.CProb _0_61)
                                   uu____11058))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___132_11135 =
                     match uu___132_11135 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l)) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____11170 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____11170 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11253 =
                                   let uu____11256 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____11257 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____11256
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11257 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_TypeChecker_Common.TProb _0_62)
                                   uu____11253))
               | (FStar_Syntax_Syntax.Tm_abs uu____11260,uu____11261) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11284 -> true
                     | uu____11299 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11327 =
                     let uu____11338 = maybe_eta t1 in
                     let uu____11343 = maybe_eta t2 in
                     (uu____11338, uu____11343) in
                   (match uu____11327 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___165_11374 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___165_11374.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___165_11374.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___165_11374.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___165_11374.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___165_11374.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___165_11374.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___165_11374.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___165_11374.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11393 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11393
                        then
                          let uu____11394 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11394 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11415 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11415
                        then
                          let uu____11416 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11416 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11421 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11432,FStar_Syntax_Syntax.Tm_abs uu____11433) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11456 -> true
                     | uu____11471 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11499 =
                     let uu____11510 = maybe_eta t1 in
                     let uu____11515 = maybe_eta t2 in
                     (uu____11510, uu____11515) in
                   (match uu____11499 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___165_11546 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___165_11546.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___165_11546.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___165_11546.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___165_11546.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___165_11546.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___165_11546.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___165_11546.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___165_11546.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11565 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11565
                        then
                          let uu____11566 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11566 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
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
                    | uu____11593 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11604,FStar_Syntax_Syntax.Tm_refine uu____11605) ->
                   let uu____11614 = as_refinement env wl t1 in
                   (match uu____11614 with
                    | (x1,phi1) ->
                        let uu____11619 = as_refinement env wl t2 in
                        (match uu____11619 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11625 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_63  ->
                                    FStar_TypeChecker_Common.TProb _0_63)
                                 uu____11625 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____11658 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____11658
                                 (guard_on_element wl problem x11) in
                             let fallback uu____11662 =
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
                                 let uu____11668 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____11668 impl in
                               let wl1 = solve_prob orig (Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11675 =
                                   let uu____11678 =
                                     let uu____11679 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____11679 :: (p_scope orig) in
                                   mk_problem uu____11678 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____11675 in
                               let uu____11682 =
                                 solve env1
                                   (let uu___166_11683 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___166_11683.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___166_11683.smt_ok);
                                      tcenv = (uu___166_11683.tcenv)
                                    }) in
                               (match uu____11682 with
                                | Failed uu____11687 -> fallback ()
                                | Success uu____11690 ->
                                    let guard =
                                      let uu____11694 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives.fst in
                                      let uu____11697 =
                                        let uu____11698 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives.fst in
                                        FStar_All.pipe_right uu____11698
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____11694
                                        uu____11697 in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl2 =
                                      let uu___167_11705 = wl1 in
                                      {
                                        attempting =
                                          (uu___167_11705.attempting);
                                        wl_deferred =
                                          (uu___167_11705.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___167_11705.defer_ok);
                                        smt_ok = (uu___167_11705.smt_ok);
                                        tcenv = (uu___167_11705.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11707,FStar_Syntax_Syntax.Tm_uvar uu____11708) ->
                   let uu____11725 = destruct_flex_t t1 in
                   let uu____11726 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11725 uu____11726
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11727;
                     FStar_Syntax_Syntax.tk = uu____11728;
                     FStar_Syntax_Syntax.pos = uu____11729;
                     FStar_Syntax_Syntax.vars = uu____11730;_},uu____11731),FStar_Syntax_Syntax.Tm_uvar
                  uu____11732) ->
                   let uu____11763 = destruct_flex_t t1 in
                   let uu____11764 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11763 uu____11764
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11765,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11766;
                     FStar_Syntax_Syntax.tk = uu____11767;
                     FStar_Syntax_Syntax.pos = uu____11768;
                     FStar_Syntax_Syntax.vars = uu____11769;_},uu____11770))
                   ->
                   let uu____11801 = destruct_flex_t t1 in
                   let uu____11802 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11801 uu____11802
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11803;
                     FStar_Syntax_Syntax.tk = uu____11804;
                     FStar_Syntax_Syntax.pos = uu____11805;
                     FStar_Syntax_Syntax.vars = uu____11806;_},uu____11807),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11808;
                     FStar_Syntax_Syntax.tk = uu____11809;
                     FStar_Syntax_Syntax.pos = uu____11810;
                     FStar_Syntax_Syntax.vars = uu____11811;_},uu____11812))
                   ->
                   let uu____11857 = destruct_flex_t t1 in
                   let uu____11858 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11857 uu____11858
               | (FStar_Syntax_Syntax.Tm_uvar uu____11859,uu____11860) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11869 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11869 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11873;
                     FStar_Syntax_Syntax.tk = uu____11874;
                     FStar_Syntax_Syntax.pos = uu____11875;
                     FStar_Syntax_Syntax.vars = uu____11876;_},uu____11877),uu____11878)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11901 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11901 t2 wl
               | (uu____11905,FStar_Syntax_Syntax.Tm_uvar uu____11906) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____11915,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11916;
                     FStar_Syntax_Syntax.tk = uu____11917;
                     FStar_Syntax_Syntax.pos = uu____11918;
                     FStar_Syntax_Syntax.vars = uu____11919;_},uu____11920))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11943,FStar_Syntax_Syntax.Tm_type uu____11944) ->
                   solve_t' env
                     (let uu___168_11953 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_11953.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_11953.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_11953.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_11953.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_11953.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_11953.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_11953.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_11953.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_11953.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11954;
                     FStar_Syntax_Syntax.tk = uu____11955;
                     FStar_Syntax_Syntax.pos = uu____11956;
                     FStar_Syntax_Syntax.vars = uu____11957;_},uu____11958),FStar_Syntax_Syntax.Tm_type
                  uu____11959) ->
                   solve_t' env
                     (let uu___168_11982 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_11982.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_11982.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_11982.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_11982.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_11982.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_11982.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_11982.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_11982.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_11982.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11983,FStar_Syntax_Syntax.Tm_arrow uu____11984) ->
                   solve_t' env
                     (let uu___168_12000 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_12000.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_12000.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_12000.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_12000.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_12000.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_12000.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_12000.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_12000.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_12000.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12001;
                     FStar_Syntax_Syntax.tk = uu____12002;
                     FStar_Syntax_Syntax.pos = uu____12003;
                     FStar_Syntax_Syntax.vars = uu____12004;_},uu____12005),FStar_Syntax_Syntax.Tm_arrow
                  uu____12006) ->
                   solve_t' env
                     (let uu___168_12036 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_12036.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_12036.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_12036.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_12036.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_12036.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_12036.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_12036.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_12036.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_12036.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____12037,uu____12038) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12049 =
                        let uu____12050 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12050 in
                      if uu____12049
                      then
                        let uu____12051 =
                          FStar_All.pipe_left
                            (fun _0_65  ->
                               FStar_TypeChecker_Common.TProb _0_65)
                            (let uu___169_12054 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_12054.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_12054.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_12054.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_12054.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_12054.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___169_12054.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_12054.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_12054.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_12054.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12055 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12051 uu____12055 t2
                          wl
                      else
                        (let uu____12060 = base_and_refinement env wl t2 in
                         match uu____12060 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12090 =
                                    FStar_All.pipe_left
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66)
                                      (let uu___170_12093 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___170_12093.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___170_12093.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___170_12093.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___170_12093.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___170_12093.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___170_12093.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___170_12093.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___170_12093.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___170_12093.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12094 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12090
                                    uu____12094 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___171_12109 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___171_12109.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___171_12109.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12112 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67)
                                      uu____12112 in
                                  let guard =
                                    let uu____12120 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12120
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12126;
                     FStar_Syntax_Syntax.tk = uu____12127;
                     FStar_Syntax_Syntax.pos = uu____12128;
                     FStar_Syntax_Syntax.vars = uu____12129;_},uu____12130),uu____12131)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12156 =
                        let uu____12157 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12157 in
                      if uu____12156
                      then
                        let uu____12158 =
                          FStar_All.pipe_left
                            (fun _0_68  ->
                               FStar_TypeChecker_Common.TProb _0_68)
                            (let uu___169_12161 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_12161.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_12161.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_12161.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_12161.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_12161.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___169_12161.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_12161.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_12161.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_12161.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12162 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12158 uu____12162 t2
                          wl
                      else
                        (let uu____12167 = base_and_refinement env wl t2 in
                         match uu____12167 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12197 =
                                    FStar_All.pipe_left
                                      (fun _0_69  ->
                                         FStar_TypeChecker_Common.TProb _0_69)
                                      (let uu___170_12200 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___170_12200.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___170_12200.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___170_12200.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___170_12200.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___170_12200.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___170_12200.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___170_12200.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___170_12200.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___170_12200.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12201 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12197
                                    uu____12201 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___171_12216 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___171_12216.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___171_12216.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12219 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_70  ->
                                         FStar_TypeChecker_Common.TProb _0_70)
                                      uu____12219 in
                                  let guard =
                                    let uu____12227 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12227
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12233,FStar_Syntax_Syntax.Tm_uvar uu____12234) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12244 = base_and_refinement env wl t1 in
                      match uu____12244 with
                      | (t_base,uu____12255) ->
                          solve_t env
                            (let uu___172_12270 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___172_12270.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___172_12270.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___172_12270.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___172_12270.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___172_12270.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___172_12270.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___172_12270.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___172_12270.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12273,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12274;
                     FStar_Syntax_Syntax.tk = uu____12275;
                     FStar_Syntax_Syntax.pos = uu____12276;
                     FStar_Syntax_Syntax.vars = uu____12277;_},uu____12278))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12302 = base_and_refinement env wl t1 in
                      match uu____12302 with
                      | (t_base,uu____12313) ->
                          solve_t env
                            (let uu___172_12328 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___172_12328.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___172_12328.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___172_12328.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___172_12328.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___172_12328.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___172_12328.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___172_12328.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___172_12328.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12331,uu____12332) ->
                   let t21 =
                     let uu____12340 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____12340 in
                   solve_t env
                     (let uu___173_12353 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_12353.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___173_12353.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___173_12353.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___173_12353.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_12353.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_12353.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_12353.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_12353.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_12353.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12354,FStar_Syntax_Syntax.Tm_refine uu____12355) ->
                   let t11 =
                     let uu____12363 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____12363 in
                   solve_t env
                     (let uu___174_12376 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_12376.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___174_12376.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___174_12376.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___174_12376.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_12376.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_12376.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_12376.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_12376.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_12376.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12379,uu____12380) ->
                   let head1 =
                     let uu____12399 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12399 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12430 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12430 FStar_Pervasives.fst in
                   let uu____12458 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12458
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12467 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12467
                      then
                        let guard =
                          let uu____12474 =
                            let uu____12475 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12475 = FStar_Syntax_Util.Equal in
                          if uu____12474
                          then None
                          else
                            (let uu____12478 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_71  -> Some _0_71)
                               uu____12478) in
                        let uu____12480 = solve_prob orig guard [] wl in
                        solve env uu____12480
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12483,uu____12484) ->
                   let head1 =
                     let uu____12492 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12492 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12523 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12523 FStar_Pervasives.fst in
                   let uu____12551 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12551
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12560 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12560
                      then
                        let guard =
                          let uu____12567 =
                            let uu____12568 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12568 = FStar_Syntax_Util.Equal in
                          if uu____12567
                          then None
                          else
                            (let uu____12571 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_72  -> Some _0_72)
                               uu____12571) in
                        let uu____12573 = solve_prob orig guard [] wl in
                        solve env uu____12573
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12576,uu____12577) ->
                   let head1 =
                     let uu____12581 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12581 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12612 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12612 FStar_Pervasives.fst in
                   let uu____12640 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12640
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12649 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12649
                      then
                        let guard =
                          let uu____12656 =
                            let uu____12657 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12657 = FStar_Syntax_Util.Equal in
                          if uu____12656
                          then None
                          else
                            (let uu____12660 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_73  -> Some _0_73)
                               uu____12660) in
                        let uu____12662 = solve_prob orig guard [] wl in
                        solve env uu____12662
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12665,uu____12666) ->
                   let head1 =
                     let uu____12670 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12670 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12701 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12701 FStar_Pervasives.fst in
                   let uu____12729 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12729
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12738 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12738
                      then
                        let guard =
                          let uu____12745 =
                            let uu____12746 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12746 = FStar_Syntax_Util.Equal in
                          if uu____12745
                          then None
                          else
                            (let uu____12749 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_74  -> Some _0_74)
                               uu____12749) in
                        let uu____12751 = solve_prob orig guard [] wl in
                        solve env uu____12751
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____12754,uu____12755) ->
                   let head1 =
                     let uu____12759 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12759 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12790 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12790 FStar_Pervasives.fst in
                   let uu____12818 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12818
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12827 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12827
                      then
                        let guard =
                          let uu____12834 =
                            let uu____12835 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12835 = FStar_Syntax_Util.Equal in
                          if uu____12834
                          then None
                          else
                            (let uu____12838 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_75  -> Some _0_75)
                               uu____12838) in
                        let uu____12840 = solve_prob orig guard [] wl in
                        solve env uu____12840
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____12843,uu____12844) ->
                   let head1 =
                     let uu____12857 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12857 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12888 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12888 FStar_Pervasives.fst in
                   let uu____12916 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12916
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12925 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12925
                      then
                        let guard =
                          let uu____12932 =
                            let uu____12933 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12933 = FStar_Syntax_Util.Equal in
                          if uu____12932
                          then None
                          else
                            (let uu____12936 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_76  -> Some _0_76)
                               uu____12936) in
                        let uu____12938 = solve_prob orig guard [] wl in
                        solve env uu____12938
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12941,FStar_Syntax_Syntax.Tm_match uu____12942) ->
                   let head1 =
                     let uu____12961 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12961 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12992 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12992 FStar_Pervasives.fst in
                   let uu____13020 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13020
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13029 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13029
                      then
                        let guard =
                          let uu____13036 =
                            let uu____13037 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13037 = FStar_Syntax_Util.Equal in
                          if uu____13036
                          then None
                          else
                            (let uu____13040 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_77  -> Some _0_77)
                               uu____13040) in
                        let uu____13042 = solve_prob orig guard [] wl in
                        solve env uu____13042
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13045,FStar_Syntax_Syntax.Tm_uinst uu____13046) ->
                   let head1 =
                     let uu____13054 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13054 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13085 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13085 FStar_Pervasives.fst in
                   let uu____13113 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13113
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13122 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13122
                      then
                        let guard =
                          let uu____13129 =
                            let uu____13130 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13130 = FStar_Syntax_Util.Equal in
                          if uu____13129
                          then None
                          else
                            (let uu____13133 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_78  -> Some _0_78)
                               uu____13133) in
                        let uu____13135 = solve_prob orig guard [] wl in
                        solve env uu____13135
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13138,FStar_Syntax_Syntax.Tm_name uu____13139) ->
                   let head1 =
                     let uu____13143 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13143 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13174 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13174 FStar_Pervasives.fst in
                   let uu____13202 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13202
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13211 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13211
                      then
                        let guard =
                          let uu____13218 =
                            let uu____13219 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13219 = FStar_Syntax_Util.Equal in
                          if uu____13218
                          then None
                          else
                            (let uu____13222 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_79  -> Some _0_79)
                               uu____13222) in
                        let uu____13224 = solve_prob orig guard [] wl in
                        solve env uu____13224
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13227,FStar_Syntax_Syntax.Tm_constant uu____13228) ->
                   let head1 =
                     let uu____13232 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13232 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13263 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13263 FStar_Pervasives.fst in
                   let uu____13291 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13291
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13300 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13300
                      then
                        let guard =
                          let uu____13307 =
                            let uu____13308 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13308 = FStar_Syntax_Util.Equal in
                          if uu____13307
                          then None
                          else
                            (let uu____13311 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_80  -> Some _0_80)
                               uu____13311) in
                        let uu____13313 = solve_prob orig guard [] wl in
                        solve env uu____13313
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13316,FStar_Syntax_Syntax.Tm_fvar uu____13317) ->
                   let head1 =
                     let uu____13321 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13321 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13352 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13352 FStar_Pervasives.fst in
                   let uu____13380 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13380
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13389 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13389
                      then
                        let guard =
                          let uu____13396 =
                            let uu____13397 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13397 = FStar_Syntax_Util.Equal in
                          if uu____13396
                          then None
                          else
                            (let uu____13400 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_81  -> Some _0_81)
                               uu____13400) in
                        let uu____13402 = solve_prob orig guard [] wl in
                        solve env uu____13402
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13405,FStar_Syntax_Syntax.Tm_app uu____13406) ->
                   let head1 =
                     let uu____13419 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13419 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13450 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13450 FStar_Pervasives.fst in
                   let uu____13478 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13478
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13487 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13487
                      then
                        let guard =
                          let uu____13494 =
                            let uu____13495 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13495 = FStar_Syntax_Util.Equal in
                          if uu____13494
                          then None
                          else
                            (let uu____13498 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_82  -> Some _0_82)
                               uu____13498) in
                        let uu____13500 = solve_prob orig guard [] wl in
                        solve env uu____13500
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13504,uu____13505),uu____13506) ->
                   solve_t' env
                     (let uu___175_13535 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_13535.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_13535.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_13535.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_13535.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_13535.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_13535.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_13535.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_13535.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_13535.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13538,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13540,uu____13541)) ->
                   solve_t' env
                     (let uu___176_13570 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_13570.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___176_13570.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___176_13570.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___176_13570.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_13570.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_13570.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_13570.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_13570.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_13570.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13571,uu____13572) ->
                   let uu____13580 =
                     let uu____13581 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13582 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13581
                       uu____13582 in
                   failwith uu____13580
               | (FStar_Syntax_Syntax.Tm_meta uu____13583,uu____13584) ->
                   let uu____13589 =
                     let uu____13590 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13591 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13590
                       uu____13591 in
                   failwith uu____13589
               | (FStar_Syntax_Syntax.Tm_delayed uu____13592,uu____13593) ->
                   let uu____13614 =
                     let uu____13615 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13616 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13615
                       uu____13616 in
                   failwith uu____13614
               | (uu____13617,FStar_Syntax_Syntax.Tm_meta uu____13618) ->
                   let uu____13623 =
                     let uu____13624 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13625 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13624
                       uu____13625 in
                   failwith uu____13623
               | (uu____13626,FStar_Syntax_Syntax.Tm_delayed uu____13627) ->
                   let uu____13648 =
                     let uu____13649 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13650 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13649
                       uu____13650 in
                   failwith uu____13648
               | (uu____13651,FStar_Syntax_Syntax.Tm_let uu____13652) ->
                   let uu____13660 =
                     let uu____13661 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13662 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13661
                       uu____13662 in
                   failwith uu____13660
               | uu____13663 -> giveup env "head tag mismatch" orig)))
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
          (let uu____13695 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____13695
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____13703  ->
                  fun uu____13704  ->
                    match (uu____13703, uu____13704) with
                    | ((a1,uu____13714),(a2,uu____13716)) ->
                        let uu____13721 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_83  -> FStar_TypeChecker_Common.TProb _0_83)
                          uu____13721)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____13727 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p) FStar_Pervasives.fst)
                 sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____13727 in
           let wl1 = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____13747 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____13754)::[] -> wp1
              | uu____13767 ->
                  let uu____13773 =
                    let uu____13774 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____13774 in
                  failwith uu____13773 in
            let uu____13777 =
              let uu____13783 =
                let uu____13784 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____13784 in
              [uu____13783] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____13777;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____13785 = lift_c1 () in solve_eq uu____13785 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___133_13789  ->
                       match uu___133_13789 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____13790 -> false)) in
             let uu____13791 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____13815)::uu____13816,(wp2,uu____13818)::uu____13819)
                   -> (wp1, wp2)
               | uu____13860 ->
                   let uu____13873 =
                     let uu____13874 =
                       let uu____13877 =
                         let uu____13878 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____13879 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____13878 uu____13879 in
                       (uu____13877, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____13874 in
                   raise uu____13873 in
             match uu____13791 with
             | (wpc1,wpc2) ->
                 let uu____13896 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____13896
                 then
                   let uu____13899 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env uu____13899 wl
                 else
                   (let uu____13903 =
                      let uu____13907 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____13907 in
                    match uu____13903 with
                    | (c2_decl,qualifiers) ->
                        let uu____13919 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____13919
                        then
                          let c1_repr =
                            let uu____13922 =
                              let uu____13923 =
                                let uu____13924 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____13924 in
                              let uu____13925 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13923 uu____13925 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13922 in
                          let c2_repr =
                            let uu____13927 =
                              let uu____13928 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____13929 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13928 uu____13929 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13927 in
                          let prob =
                            let uu____13931 =
                              let uu____13934 =
                                let uu____13935 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____13936 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____13935
                                  uu____13936 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____13934 in
                            FStar_TypeChecker_Common.TProb uu____13931 in
                          let wl1 =
                            let uu____13938 =
                              let uu____13940 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives.fst in
                              Some uu____13940 in
                            solve_prob orig uu____13938 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____13947 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____13947
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____13949 =
                                     let uu____13952 =
                                       let uu____13953 =
                                         let uu____13963 =
                                           let uu____13964 =
                                             let uu____13965 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____13965] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____13964 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____13966 =
                                           let uu____13968 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____13969 =
                                             let uu____13971 =
                                               let uu____13972 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____13972 in
                                             [uu____13971] in
                                           uu____13968 :: uu____13969 in
                                         (uu____13963, uu____13966) in
                                       FStar_Syntax_Syntax.Tm_app uu____13953 in
                                     FStar_Syntax_Syntax.mk uu____13952 in
                                   uu____13949
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____13983 =
                                    let uu____13986 =
                                      let uu____13987 =
                                        let uu____13997 =
                                          let uu____13998 =
                                            let uu____13999 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____13999] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____13998 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____14000 =
                                          let uu____14002 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____14003 =
                                            let uu____14005 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____14006 =
                                              let uu____14008 =
                                                let uu____14009 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14009 in
                                              [uu____14008] in
                                            uu____14005 :: uu____14006 in
                                          uu____14002 :: uu____14003 in
                                        (uu____13997, uu____14000) in
                                      FStar_Syntax_Syntax.Tm_app uu____13987 in
                                    FStar_Syntax_Syntax.mk uu____13986 in
                                  uu____13983
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____14020 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_TypeChecker_Common.TProb _0_84)
                               uu____14020 in
                           let wl1 =
                             let uu____14026 =
                               let uu____14028 =
                                 let uu____14031 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____14031 g in
                               FStar_All.pipe_left (fun _0_85  -> Some _0_85)
                                 uu____14028 in
                             solve_prob orig uu____14026 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____14041 = FStar_Util.physical_equality c1 c2 in
        if uu____14041
        then
          let uu____14042 = solve_prob orig None [] wl in
          solve env uu____14042
        else
          ((let uu____14045 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____14045
            then
              let uu____14046 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____14047 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14046
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14047
            else ());
           (let uu____14049 =
              let uu____14052 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____14053 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____14052, uu____14053) in
            match uu____14049 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14057),FStar_Syntax_Syntax.Total
                    (t2,uu____14059)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14072 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14072 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14075,FStar_Syntax_Syntax.Total uu____14076) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14088),FStar_Syntax_Syntax.Total
                    (t2,uu____14090)) ->
                     let uu____14103 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14103 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14107),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14109)) ->
                     let uu____14122 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14122 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14126),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14128)) ->
                     let uu____14141 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14141 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14144,FStar_Syntax_Syntax.Comp uu____14145) ->
                     let uu____14151 =
                       let uu___177_14154 = problem in
                       let uu____14157 =
                         let uu____14158 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14158 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14154.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14157;
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14154.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___177_14154.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___177_14154.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14154.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14154.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14154.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14154.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14154.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14151 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14159,FStar_Syntax_Syntax.Comp uu____14160) ->
                     let uu____14166 =
                       let uu___177_14169 = problem in
                       let uu____14172 =
                         let uu____14173 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14173 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14169.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14172;
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14169.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___177_14169.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___177_14169.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14169.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14169.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14169.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14169.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14169.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14166 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14174,FStar_Syntax_Syntax.GTotal uu____14175) ->
                     let uu____14181 =
                       let uu___178_14184 = problem in
                       let uu____14187 =
                         let uu____14188 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14188 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14184.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___178_14184.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14184.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14187;
                         FStar_TypeChecker_Common.element =
                           (uu___178_14184.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14184.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14184.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14184.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14184.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14184.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14181 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14189,FStar_Syntax_Syntax.Total uu____14190) ->
                     let uu____14196 =
                       let uu___178_14199 = problem in
                       let uu____14202 =
                         let uu____14203 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14203 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14199.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___178_14199.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14199.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14202;
                         FStar_TypeChecker_Common.element =
                           (uu___178_14199.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14199.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14199.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14199.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14199.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14199.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14196 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14204,FStar_Syntax_Syntax.Comp uu____14205) ->
                     let uu____14206 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____14206
                     then
                       let uu____14207 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type" in
                       solve_t env uu____14207 wl
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
                           (let uu____14217 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____14217
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14219 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____14219 with
                            | None  ->
                                let uu____14221 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14222 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____14222) in
                                if uu____14221
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
                                  (let uu____14225 =
                                     let uu____14226 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____14227 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14226 uu____14227 in
                                   giveup env uu____14225 orig)
                            | Some edge -> solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14232 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14248  ->
              match uu____14248 with
              | (uu____14255,uu____14256,u,uu____14258,uu____14259,uu____14260)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____14232 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14278 =
        FStar_All.pipe_right (fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____14278 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____14288 =
        FStar_All.pipe_right (snd ineqs)
          (FStar_List.map
             (fun uu____14300  ->
                match uu____14300 with
                | (u1,u2) ->
                    let uu____14305 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____14306 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____14305 uu____14306)) in
      FStar_All.pipe_right uu____14288 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14318,[])) -> "{}"
      | uu____14331 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14341 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____14341
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____14344 =
              FStar_List.map
                (fun uu____14348  ->
                   match uu____14348 with
                   | (uu____14351,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____14344 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____14355 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14355 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14393 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____14393
    then
      let uu____14394 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____14395 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14394
        (rel_to_string rel) uu____14395
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
            let uu____14415 =
              let uu____14417 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_86  -> Some _0_86) uu____14417 in
            FStar_Syntax_Syntax.new_bv uu____14415 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____14423 =
              let uu____14425 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_87  -> Some _0_87) uu____14425 in
            let uu____14427 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____14423 uu____14427 in
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
          let uu____14450 = FStar_Options.eager_inference () in
          if uu____14450
          then
            let uu___179_14451 = probs in
            {
              attempting = (uu___179_14451.attempting);
              wl_deferred = (uu___179_14451.wl_deferred);
              ctr = (uu___179_14451.ctr);
              defer_ok = false;
              smt_ok = (uu___179_14451.smt_ok);
              tcenv = (uu___179_14451.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Syntax_Unionfind.rollback tx;
             (let uu____14462 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____14462
              then
                let uu____14463 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____14463
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
          ((let uu____14473 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____14473
            then
              let uu____14474 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14474
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____14478 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____14478
             then
               let uu____14479 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14479
             else ());
            (let f2 =
               let uu____14482 =
                 let uu____14483 = FStar_Syntax_Util.unmeta f1 in
                 uu____14483.FStar_Syntax_Syntax.n in
               match uu____14482 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14487 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___180_14488 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___180_14488.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___180_14488.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___180_14488.FStar_TypeChecker_Env.implicits)
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
            let uu____14503 =
              let uu____14504 =
                let uu____14505 =
                  let uu____14506 =
                    FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____14506
                    (fun _0_88  -> FStar_TypeChecker_Common.NonTrivial _0_88) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14505;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____14504 in
            FStar_All.pipe_left (fun _0_89  -> Some _0_89) uu____14503
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____14539 =
        let uu____14540 =
          let uu____14541 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
          FStar_All.pipe_right uu____14541
            (fun _0_90  -> FStar_TypeChecker_Common.NonTrivial _0_90) in
        {
          FStar_TypeChecker_Env.guard_f = uu____14540;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      Some uu____14539
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
          (let uu____14567 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14567
           then
             let uu____14568 = FStar_Syntax_Print.term_to_string t1 in
             let uu____14569 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14568
               uu____14569
           else ());
          (let prob =
             let uu____14572 =
               let uu____14575 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____14575 in
             FStar_All.pipe_left
               (fun _0_91  -> FStar_TypeChecker_Common.TProb _0_91)
               uu____14572 in
           let g =
             let uu____14580 =
               let uu____14582 = singleton' env prob smt_ok in
               solve_and_commit env uu____14582 (fun uu____14583  -> None) in
             FStar_All.pipe_left (with_guard env prob) uu____14580 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14597 = try_teq true env t1 t2 in
        match uu____14597 with
        | None  ->
            let uu____14599 =
              let uu____14600 =
                let uu____14603 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                let uu____14604 = FStar_TypeChecker_Env.get_range env in
                (uu____14603, uu____14604) in
              FStar_Errors.Error uu____14600 in
            raise uu____14599
        | Some g ->
            ((let uu____14607 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____14607
              then
                let uu____14608 = FStar_Syntax_Print.term_to_string t1 in
                let uu____14609 = FStar_Syntax_Print.term_to_string t2 in
                let uu____14610 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14608
                  uu____14609 uu____14610
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
          (let uu____14626 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14626
           then
             let uu____14627 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____14628 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14627
               uu____14628
           else ());
          (let uu____14630 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____14630 with
           | (prob,x) ->
               let g =
                 let uu____14638 =
                   let uu____14640 = singleton' env prob smt_ok in
                   solve_and_commit env uu____14640
                     (fun uu____14641  -> None) in
                 FStar_All.pipe_left (with_guard env prob) uu____14638 in
               ((let uu____14647 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____14647
                 then
                   let uu____14648 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____14649 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____14650 =
                     let uu____14651 = FStar_Util.must g in
                     guard_to_string env uu____14651 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14648 uu____14649 uu____14650
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
          let uu____14675 = FStar_TypeChecker_Env.get_range env in
          let uu____14676 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.err uu____14675 uu____14676
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____14688 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____14688
         then
           let uu____14689 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____14690 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____14689
             uu____14690
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____14695 =
             let uu____14698 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None uu____14698 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_92  -> FStar_TypeChecker_Common.CProb _0_92) uu____14695 in
         let uu____14701 =
           let uu____14703 = singleton env prob in
           solve_and_commit env uu____14703 (fun uu____14704  -> None) in
         FStar_All.pipe_left (with_guard env prob) uu____14701)
let solve_universe_inequalities':
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____14723  ->
        match uu____14723 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____14748 =
                 let uu____14749 =
                   let uu____14752 =
                     let uu____14753 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____14754 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____14753 uu____14754 in
                   let uu____14755 = FStar_TypeChecker_Env.get_range env in
                   (uu____14752, uu____14755) in
                 FStar_Errors.Error uu____14749 in
               raise uu____14748) in
            let equiv1 v1 v' =
              let uu____14763 =
                let uu____14766 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____14767 = FStar_Syntax_Subst.compress_univ v' in
                (uu____14766, uu____14767) in
              match uu____14763 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____14774 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____14788 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____14788 with
                      | FStar_Syntax_Syntax.U_unif uu____14792 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____14803  ->
                                    match uu____14803 with
                                    | (u,v') ->
                                        let uu____14809 = equiv1 v1 v' in
                                        if uu____14809
                                        then
                                          let uu____14811 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____14811 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____14821 -> [])) in
            let uu____14824 =
              let wl =
                let uu___181_14827 = empty_worklist env in
                {
                  attempting = (uu___181_14827.attempting);
                  wl_deferred = (uu___181_14827.wl_deferred);
                  ctr = (uu___181_14827.ctr);
                  defer_ok = false;
                  smt_ok = (uu___181_14827.smt_ok);
                  tcenv = (uu___181_14827.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____14834  ->
                      match uu____14834 with
                      | (lb,v1) ->
                          let uu____14839 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____14839 with
                           | USolved wl1 -> ()
                           | uu____14841 -> fail lb v1))) in
            let rec check_ineq uu____14847 =
              match uu____14847 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____14854) -> true
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
                      uu____14865,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____14867,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____14872) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____14876,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____14881 -> false) in
            let uu____14884 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____14890  ->
                      match uu____14890 with
                      | (u,v1) ->
                          let uu____14895 = check_ineq (u, v1) in
                          if uu____14895
                          then true
                          else
                            ((let uu____14898 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____14898
                              then
                                let uu____14899 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____14900 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____14899
                                  uu____14900
                              else ());
                             false))) in
            if uu____14884
            then ()
            else
              ((let uu____14904 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____14904
                then
                  ((let uu____14906 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____14906);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____14912 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____14912))
                else ());
               (let uu____14918 =
                  let uu____14919 =
                    let uu____14922 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____14922) in
                  FStar_Errors.Error uu____14919 in
                raise uu____14918))
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
      let fail uu____14955 =
        match uu____14955 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____14965 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____14965
       then
         let uu____14966 = wl_to_string wl in
         let uu____14967 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____14966 uu____14967
       else ());
      (let g1 =
         let uu____14982 = solve_and_commit env wl fail in
         match uu____14982 with
         | Some [] ->
             let uu___182_14989 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___182_14989.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___182_14989.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___182_14989.FStar_TypeChecker_Env.implicits)
             }
         | uu____14992 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___183_14995 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___183_14995.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___183_14995.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___183_14995.FStar_TypeChecker_Env.implicits)
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
            let uu___184_15021 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___184_15021.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___184_15021.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___184_15021.FStar_TypeChecker_Env.implicits)
            } in
          let uu____15022 =
            let uu____15023 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____15023 in
          if uu____15022
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15029 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____15029
                   then
                     let uu____15030 = FStar_TypeChecker_Env.get_range env in
                     let uu____15031 =
                       let uu____15032 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15032 in
                     FStar_Errors.diag uu____15030 uu____15031
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding] env vc in
                   let uu____15035 = check_trivial vc1 in
                   match uu____15035 with
                   | FStar_TypeChecker_Common.Trivial  -> Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then None
                       else
                         ((let uu____15042 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15042
                           then
                             let uu____15043 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____15044 =
                               let uu____15045 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15045 in
                             FStar_Errors.diag uu____15043 uu____15044
                           else ());
                          (let vcs =
                             let uu____15051 = FStar_Options.use_tactics () in
                             if uu____15051
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)] in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____15065  ->
                                   match uu____15065 with
                                   | (env1,goal) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify]
                                           env1 goal in
                                       let uu____15071 = check_trivial goal1 in
                                       (match uu____15071 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____15073 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____15073
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                                               ();
                                             (let uu____15078 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____15078
                                              then
                                                let uu____15079 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____15080 =
                                                  let uu____15081 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____15082 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____15081 uu____15082 in
                                                FStar_Errors.diag uu____15079
                                                  uu____15080
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
      let uu____15090 = discharge_guard' None env g false in
      match uu____15090 with
      | Some g1 -> g1
      | None  ->
          let uu____15095 =
            let uu____15096 =
              let uu____15099 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____15099) in
            FStar_Errors.Error uu____15096 in
          raise uu____15095
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15106 = discharge_guard' None env g true in
      match uu____15106 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____15118 = FStar_Syntax_Unionfind.find u in
      match uu____15118 with | None  -> true | uu____15120 -> false in
    let rec until_fixpoint acc implicits =
      let uu____15133 = acc in
      match uu____15133 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____15179 = hd1 in
               (match uu____15179 with
                | (uu____15186,env,u,tm,k,r) ->
                    let uu____15192 = unresolved u in
                    if uu____15192
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm in
                       (let uu____15210 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck") in
                        if uu____15210
                        then
                          let uu____15211 =
                            FStar_Syntax_Print.uvar_to_string u in
                          let uu____15212 =
                            FStar_Syntax_Print.term_to_string tm1 in
                          let uu____15213 =
                            FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____15211 uu____15212 uu____15213
                        else ());
                       (let uu____15215 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___185_15219 = env1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___185_15219.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___185_15219.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___185_15219.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___185_15219.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___185_15219.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___185_15219.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___185_15219.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___185_15219.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___185_15219.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___185_15219.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___185_15219.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___185_15219.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___185_15219.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___185_15219.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___185_15219.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___185_15219.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___185_15219.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___185_15219.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___185_15219.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___185_15219.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___185_15219.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___185_15219.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___185_15219.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___185_15219.FStar_TypeChecker_Env.proof_ns)
                             }) tm1 in
                        match uu____15215 with
                        | (uu____15220,uu____15221,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___186_15224 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___186_15224.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___186_15224.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___186_15224.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____15227 =
                                discharge_guard'
                                  (Some
                                     (fun uu____15231  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____15227 with
                              | Some g3 -> g3
                              | None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
    let uu___187_15246 = g in
    let uu____15247 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___187_15246.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___187_15246.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___187_15246.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____15247
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____15275 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____15275 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15282 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15282
      | (reason,uu____15284,uu____15285,e,t,r)::uu____15289 ->
          let uu____15303 =
            let uu____15304 = FStar_Syntax_Print.term_to_string t in
            let uu____15305 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format3
              "Failed to resolve implicit argument of type '%s' introduced in %s because %s"
              uu____15304 uu____15305 reason in
          FStar_Errors.err r uu____15303
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___188_15312 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___188_15312.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___188_15312.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___188_15312.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15330 = try_teq false env t1 t2 in
        match uu____15330 with
        | None  -> false
        | Some g ->
            let uu____15333 = discharge_guard' None env g false in
            (match uu____15333 with
             | Some uu____15337 -> true
             | None  -> false)