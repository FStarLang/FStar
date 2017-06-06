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
    match projectee with | TERM _0 -> true | uu____408 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
      FStar_Syntax_Syntax.term)
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____434 -> false
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
    match projectee with | Success _0 -> true | uu____522 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____536 -> false
let __proj__Failed__item___0:
  solution -> (FStar_TypeChecker_Common.prob* Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0
type variance =
  | COVARIANT
  | CONTRAVARIANT
  | INVARIANT
let uu___is_COVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____553 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____557 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____561 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___106_578  ->
    match uu___106_578 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____591 =
    let uu____592 = FStar_Syntax_Subst.compress t in
    uu____592.FStar_Syntax_Syntax.n in
  match uu____591 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____609 = FStar_Syntax_Print.uvar_to_string u in
      let uu____610 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____609 uu____610
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____613;
         FStar_Syntax_Syntax.pos = uu____614;
         FStar_Syntax_Syntax.vars = uu____615;_},args)
      ->
      let uu____643 = FStar_Syntax_Print.uvar_to_string u in
      let uu____644 = FStar_Syntax_Print.term_to_string ty in
      let uu____645 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" uu____643 uu____644 uu____645
  | uu____646 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___107_652  ->
      match uu___107_652 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____656 =
            let uu____658 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____659 =
              let uu____661 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____662 =
                let uu____664 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____665 =
                  let uu____667 =
                    let uu____669 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____670 =
                      let uu____672 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____673 =
                        let uu____675 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (fst p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____676 =
                          let uu____678 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____678] in
                        uu____675 :: uu____676 in
                      uu____672 :: uu____673 in
                    uu____669 :: uu____670 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____667 in
                uu____664 :: uu____665 in
              uu____661 :: uu____662 in
            uu____658 :: uu____659 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____656
      | FStar_TypeChecker_Common.CProb p ->
          let uu____683 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____684 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____683
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____684
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___108_690  ->
      match uu___108_690 with
      | UNIV (u,t) ->
          let x =
            let uu____694 = FStar_Options.hide_uvar_nums () in
            if uu____694
            then "?"
            else
              (let uu____696 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____696 FStar_Util.string_of_int) in
          let uu____697 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____697
      | TERM ((u,uu____699),t) ->
          let x =
            let uu____704 = FStar_Options.hide_uvar_nums () in
            if uu____704
            then "?"
            else
              (let uu____706 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____706 FStar_Util.string_of_int) in
          let uu____707 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____707
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____716 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____716 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____724 =
      let uu____726 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____726
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____724 (FStar_String.concat ", ")
let args_to_string args =
  let uu____744 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____752  ->
            match uu____752 with
            | (x,uu____756) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right uu____744 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____761 =
      let uu____762 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____762 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____761;
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
        let uu___139_775 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___139_775.wl_deferred);
          ctr = (uu___139_775.ctr);
          defer_ok = (uu___139_775.defer_ok);
          smt_ok;
          tcenv = (uu___139_775.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___140_800 = empty_worklist env in
  let uu____801 = FStar_List.map FStar_Pervasives.snd g in
  {
    attempting = uu____801;
    wl_deferred = (uu___140_800.wl_deferred);
    ctr = (uu___140_800.ctr);
    defer_ok = false;
    smt_ok = (uu___140_800.smt_ok);
    tcenv = (uu___140_800.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___141_813 = wl in
        {
          attempting = (uu___141_813.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___141_813.ctr);
          defer_ok = (uu___141_813.defer_ok);
          smt_ok = (uu___141_813.smt_ok);
          tcenv = (uu___141_813.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___142_825 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___142_825.wl_deferred);
        ctr = (uu___142_825.ctr);
        defer_ok = (uu___142_825.defer_ok);
        smt_ok = (uu___142_825.smt_ok);
        tcenv = (uu___142_825.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____836 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____836
         then
           let uu____837 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____837
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___109_841  ->
    match uu___109_841 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___143_857 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___143_857.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___143_857.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___143_857.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___143_857.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___143_857.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___143_857.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___143_857.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___110_878  ->
    match uu___110_878 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_32  -> FStar_TypeChecker_Common.TProb _0_32)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_33  -> FStar_TypeChecker_Common.CProb _0_33)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___111_894  ->
      match uu___111_894 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___112_897  ->
    match uu___112_897 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___113_906  ->
    match uu___113_906 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___114_916  ->
    match uu___114_916 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___115_926  ->
    match uu___115_926 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun uu___116_937  ->
    match uu___116_937 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___117_948  ->
    match uu___117_948 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___118_957  ->
    match uu___118_957 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_34  -> FStar_TypeChecker_Common.TProb _0_34) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_35  -> FStar_TypeChecker_Common.CProb _0_35) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____971 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____971 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____982  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1032 = next_pid () in
  let uu____1033 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1032;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1033;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1080 = next_pid () in
  let uu____1081 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1080;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1081;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1122 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1122;
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
        let uu____1174 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1174
        then
          let uu____1175 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1176 = prob_to_string env d in
          let uu____1177 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1175 uu____1176 uu____1177 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1182 -> failwith "impossible" in
           let uu____1183 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1191 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1192 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1191, uu____1192)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1196 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1197 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1196, uu____1197) in
           match uu____1183 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___119_1206  ->
            match uu___119_1206 with
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
        (fun uu___120_1227  ->
           match uu___120_1227 with
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
        (fun uu___121_1249  ->
           match uu___121_1249 with
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
                    let uu___144_1315 = x in
                    let uu____1316 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___144_1315.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___144_1315.FStar_Syntax_Syntax.index);
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
    | FStar_Syntax_Syntax.Tm_let uu____1776 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_match uu____1795 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_meta uu____1822 ->
        let uu____1827 =
          let uu____1828 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1829 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1828
            uu____1829 in
        failwith uu____1827
    | FStar_Syntax_Syntax.Tm_ascribed uu____1839 ->
        let uu____1857 =
          let uu____1858 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1859 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1858
            uu____1859 in
        failwith uu____1857
    | FStar_Syntax_Syntax.Tm_delayed uu____1869 ->
        let uu____1890 =
          let uu____1891 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1892 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1891
            uu____1892 in
        failwith uu____1890
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1902 =
          let uu____1903 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1904 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1903
            uu____1904 in
        failwith uu____1902 in
  let uu____1914 = whnf env t1 in aux false uu____1914
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1923 =
        let uu____1933 = empty_worklist env in
        base_and_refinement env uu____1933 t in
      FStar_All.pipe_right uu____1923 FStar_Pervasives.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____1957 = FStar_Syntax_Syntax.null_bv t in
    (uu____1957, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____1977 = base_and_refinement env wl t in
  match uu____1977 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
let force_refinement uu____2036 =
  match uu____2036 with
  | (t_base,refopt) ->
      let uu____2050 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base in
      (match uu____2050 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___122_2074  ->
      match uu___122_2074 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2078 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2079 =
            let uu____2080 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____2080 in
          let uu____2081 =
            let uu____2082 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____2082 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2078 uu____2079
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2081
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2086 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2087 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____2088 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2086 uu____2087
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2088
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2092 =
      let uu____2094 =
        let uu____2096 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2106  ->
                  match uu____2106 with | (uu____2110,uu____2111,x) -> x)) in
        FStar_List.append wl.attempting uu____2096 in
      FStar_List.map (wl_prob_to_string wl) uu____2094 in
    FStar_All.pipe_right uu____2092 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2129 =
          let uu____2139 =
            let uu____2140 = FStar_Syntax_Subst.compress k in
            uu____2140.FStar_Syntax_Syntax.n in
          match uu____2139 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2181 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2181)
              else
                (let uu____2195 = FStar_Syntax_Util.abs_formals t in
                 match uu____2195 with
                 | (ys',t1,uu____2216) ->
                     let uu____2229 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2229))
          | uu____2250 ->
              let uu____2251 =
                let uu____2257 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____2257) in
              ((ys, t), uu____2251) in
        match uu____2129 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2312 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2312 c in
               let uu____2314 =
                 let uu____2321 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_36  -> FStar_Util.Inl _0_36) in
                 FStar_All.pipe_right uu____2321 (fun _0_37  -> Some _0_37) in
               FStar_Syntax_Util.abs ys1 t1 uu____2314)
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
            let uu____2372 = p_guard prob in
            match uu____2372 with
            | (uu____2375,uv) ->
                ((let uu____2378 =
                    let uu____2379 = FStar_Syntax_Subst.compress uv in
                    uu____2379.FStar_Syntax_Syntax.n in
                  match uu____2378 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2399 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2399
                        then
                          let uu____2400 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2401 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2402 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2400
                            uu____2401 uu____2402
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2404 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___145_2407 = wl in
                  {
                    attempting = (uu___145_2407.attempting);
                    wl_deferred = (uu___145_2407.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___145_2407.defer_ok);
                    smt_ok = (uu___145_2407.smt_ok);
                    tcenv = (uu___145_2407.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2420 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2420
         then
           let uu____2421 = FStar_Util.string_of_int pid in
           let uu____2422 =
             let uu____2423 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2423 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2421 uu____2422
         else ());
        commit sol;
        (let uu___146_2428 = wl in
         {
           attempting = (uu___146_2428.attempting);
           wl_deferred = (uu___146_2428.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___146_2428.defer_ok);
           smt_ok = (uu___146_2428.smt_ok);
           tcenv = (uu___146_2428.tcenv)
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
            | (uu____2457,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2465 = FStar_Syntax_Util.mk_conj t1 f in
                Some uu____2465 in
          (let uu____2471 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2471
           then
             let uu____2472 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2473 =
               let uu____2474 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2474 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2472 uu____2473
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2499 =
    let uu____2503 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2503 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2499
    (FStar_Util.for_some
       (fun uu____2520  ->
          match uu____2520 with
          | (uv,uu____2524) -> FStar_Syntax_Unionfind.equiv uv (fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2557 = occurs wl uk t in Prims.op_Negation uu____2557 in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2562 =
         let uu____2563 = FStar_Syntax_Print.uvar_to_string (fst uk) in
         let uu____2564 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2563 uu____2564 in
       Some uu____2562) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2612 = occurs_check env wl uk t in
  match uu____2612 with
  | (occurs_ok,msg) ->
      let uu____2629 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2629, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2693 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2717  ->
            fun uu____2718  ->
              match (uu____2717, uu____2718) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2761 =
                    let uu____2762 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2762 in
                  if uu____2761
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2776 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2776
                     then
                       let uu____2783 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____2783)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2693 with | (isect,uu____2805) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2854  ->
          fun uu____2855  ->
            match (uu____2854, uu____2855) with
            | ((a,uu____2865),(b,uu____2867)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2911 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2917  ->
                match uu____2917 with
                | (b,uu____2921) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____2911 then None else Some (a, (snd hd1))
  | uu____2930 -> None
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
            let uu____2973 = pat_var_opt env seen hd1 in
            (match uu____2973 with
             | None  ->
                 ((let uu____2981 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____2981
                   then
                     let uu____2982 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____2982
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2994 =
      let uu____2995 = FStar_Syntax_Subst.compress t in
      uu____2995.FStar_Syntax_Syntax.n in
    match uu____2994 with
    | FStar_Syntax_Syntax.Tm_uvar uu____2998 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3007;
           FStar_Syntax_Syntax.tk = uu____3008;
           FStar_Syntax_Syntax.pos = uu____3009;
           FStar_Syntax_Syntax.vars = uu____3010;_},uu____3011)
        -> true
    | uu____3034 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3096;
         FStar_Syntax_Syntax.pos = uu____3097;
         FStar_Syntax_Syntax.vars = uu____3098;_},args)
      -> (t, uv, k, args)
  | uu____3139 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____3193 = destruct_flex_t t in
  match uu____3193 with
  | (t1,uv,k,args) ->
      let uu____3261 = pat_vars env [] args in
      (match uu____3261 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3317 -> ((t1, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth option*
  FStar_Syntax_Syntax.delta_depth option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3366 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth option* FStar_Syntax_Syntax.delta_depth
      option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3389 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3393 -> false
let head_match: match_result -> match_result =
  fun uu___123_3396  ->
    match uu___123_3396 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3405 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3418 ->
          let uu____3419 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3419 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3429 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3443 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3449 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> None
      | FStar_Syntax_Syntax.Tm_bvar uu____3471 -> None
      | FStar_Syntax_Syntax.Tm_name uu____3472 -> None
      | FStar_Syntax_Syntax.Tm_uvar uu____3473 -> None
      | FStar_Syntax_Syntax.Tm_let uu____3482 -> None
      | FStar_Syntax_Syntax.Tm_match uu____3490 -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3507) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3513,uu____3514) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3544) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3559;
             FStar_Syntax_Syntax.index = uu____3560;
             FStar_Syntax_Syntax.sort = t2;_},uu____3562)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3569 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3570 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3571 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3579 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3595 = fv_delta_depth env fv in Some uu____3595
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
            let uu____3614 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3614
            then FullMatch
            else
              (let uu____3616 =
                 let uu____3621 =
                   let uu____3623 = fv_delta_depth env f in Some uu____3623 in
                 let uu____3624 =
                   let uu____3626 = fv_delta_depth env g in Some uu____3626 in
                 (uu____3621, uu____3624) in
               MisMatch uu____3616)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3630),FStar_Syntax_Syntax.Tm_uinst (g,uu____3632)) ->
            let uu____3641 = head_matches env f g in
            FStar_All.pipe_right uu____3641 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3648),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3650)) ->
            let uu____3675 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____3675 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3680),FStar_Syntax_Syntax.Tm_refine (y,uu____3682)) ->
            let uu____3691 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3691 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3693),uu____3694) ->
            let uu____3699 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3699 head_match
        | (uu____3700,FStar_Syntax_Syntax.Tm_refine (x,uu____3702)) ->
            let uu____3707 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3707 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3708,FStar_Syntax_Syntax.Tm_type
           uu____3709) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3710,FStar_Syntax_Syntax.Tm_arrow uu____3711) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3727),FStar_Syntax_Syntax.Tm_app (head',uu____3729))
            ->
            let uu____3758 = head_matches env head1 head' in
            FStar_All.pipe_right uu____3758 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3760),uu____3761) ->
            let uu____3776 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____3776 head_match
        | (uu____3777,FStar_Syntax_Syntax.Tm_app (head1,uu____3779)) ->
            let uu____3794 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____3794 head_match
        | uu____3795 ->
            let uu____3798 =
              let uu____3803 = delta_depth_of_term env t11 in
              let uu____3805 = delta_depth_of_term env t21 in
              (uu____3803, uu____3805) in
            MisMatch uu____3798
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3841 = FStar_Syntax_Util.head_and_args t in
    match uu____3841 with
    | (head1,uu____3853) ->
        let uu____3868 =
          let uu____3869 = FStar_Syntax_Util.un_uinst head1 in
          uu____3869.FStar_Syntax_Syntax.n in
        (match uu____3868 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3874 =
               let uu____3875 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____3875 FStar_Option.isSome in
             if uu____3874
             then
               let uu____3889 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____3889 (fun _0_38  -> Some _0_38)
             else None
         | uu____3892 -> None) in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None)) in
  let fail r = (r, None) in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21 in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),uu____3960) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____3970 =
             let uu____3975 = maybe_inline t11 in
             let uu____3977 = maybe_inline t21 in (uu____3975, uu____3977) in
           match uu____3970 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (uu____3998,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4008 =
             let uu____4013 = maybe_inline t11 in
             let uu____4015 = maybe_inline t21 in (uu____4013, uu____4015) in
           match uu____4008 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____4040 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____4040 with
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
        let uu____4055 =
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
             let uu____4063 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____4063)) in
        (match uu____4055 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4071 -> fail r
    | uu____4076 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4105 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4135 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4150 = FStar_Syntax_Util.type_u () in
      match uu____4150 with
      | (t,uu____4154) ->
          let uu____4155 = new_uvar r binders t in fst uu____4155
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4164 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____4164 FStar_Pervasives.fst
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
        let uu____4206 = head_matches env t1 t' in
        match uu____4206 with
        | MisMatch uu____4207 -> false
        | uu____4212 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4272,imp),T (t2,uu____4275)) -> (t2, imp)
                     | uu____4292 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4332  ->
                    match uu____4332 with
                    | (t2,uu____4340) ->
                        (None, INVARIANT, (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let fail uu____4373 = failwith "Bad reconstruction" in
          let uu____4374 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____4374 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4427))::tcs2) ->
                       aux
                         (((let uu___147_4449 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___147_4449.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___147_4449.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4459 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___124_4490 =
                 match uu___124_4490 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4553 = decompose1 [] bs1 in
               (rebuild, matches, uu____4553))
      | uu____4581 ->
          let rebuild uu___125_4586 =
            match uu___125_4586 with
            | [] -> t1
            | uu____4588 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___126_4607  ->
    match uu___126_4607 with
    | T (t,uu____4609) -> t
    | uu____4618 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___127_4621  ->
    match uu___127_4621 with
    | T (t,uu____4623) -> FStar_Syntax_Syntax.as_arg t
    | uu____4632 -> failwith "Impossible"
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
              | (uu____4701,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4720 = new_uvar r scope1 k in
                  (match uu____4720 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4732 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args)) None r in
                       let uu____4747 =
                         let uu____4748 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_39  ->
                              FStar_TypeChecker_Common.TProb _0_39)
                           uu____4748 in
                       ((T (gi_xs, mk_kind)), uu____4747))
              | (uu____4757,uu____4758,C uu____4759) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4846 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4857;
                         FStar_Syntax_Syntax.pos = uu____4858;
                         FStar_Syntax_Syntax.vars = uu____4859;_})
                        ->
                        let uu____4874 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4874 with
                         | (T (gi_xs,uu____4890),prob) ->
                             let uu____4900 =
                               let uu____4901 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_40  -> C _0_40)
                                 uu____4901 in
                             (uu____4900, [prob])
                         | uu____4903 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4913;
                         FStar_Syntax_Syntax.pos = uu____4914;
                         FStar_Syntax_Syntax.vars = uu____4915;_})
                        ->
                        let uu____4930 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4930 with
                         | (T (gi_xs,uu____4946),prob) ->
                             let uu____4956 =
                               let uu____4957 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_41  -> C _0_41)
                                 uu____4957 in
                             (uu____4956, [prob])
                         | uu____4959 -> failwith "impossible")
                    | (uu____4965,uu____4966,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____4968;
                         FStar_Syntax_Syntax.pos = uu____4969;
                         FStar_Syntax_Syntax.vars = uu____4970;_})
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
                        let uu____5044 =
                          let uu____5049 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____5049 FStar_List.unzip in
                        (match uu____5044 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5078 =
                                 let uu____5079 =
                                   let uu____5082 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____5082 un_T in
                                 let uu____5083 =
                                   let uu____5089 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____5089
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5079;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5083;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5078 in
                             ((C gi_xs), sub_probs))
                    | uu____5094 ->
                        let uu____5101 = sub_prob scope1 args q in
                        (match uu____5101 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____4846 with
                   | (tc,probs) ->
                       let uu____5119 =
                         match q with
                         | (Some b,uu____5145,uu____5146) ->
                             let uu____5154 =
                               let uu____5158 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____5158 :: args in
                             ((Some b), (b :: scope1), uu____5154)
                         | uu____5176 -> (None, scope1, args) in
                       (match uu____5119 with
                        | (bopt,scope2,args1) ->
                            let uu____5219 = aux scope2 args1 qs2 in
                            (match uu____5219 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____5240 =
                                         let uu____5242 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         f :: uu____5242 in
                                       FStar_Syntax_Util.mk_conj_l uu____5240
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (fst b).FStar_Syntax_Syntax.sort in
                                       let uu____5255 =
                                         let uu____5257 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (fst b) f in
                                         let uu____5258 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         uu____5257 :: uu____5258 in
                                       FStar_Syntax_Util.mk_conj_l uu____5255 in
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
  let uu___148_5311 = p in
  let uu____5314 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____5315 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___148_5311.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5314;
    FStar_TypeChecker_Common.relation =
      (uu___148_5311.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5315;
    FStar_TypeChecker_Common.element =
      (uu___148_5311.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___148_5311.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___148_5311.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___148_5311.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___148_5311.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___148_5311.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5325 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____5325
            (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
      | FStar_TypeChecker_Common.CProb uu____5330 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5344 = compress_prob wl pr in
        FStar_All.pipe_right uu____5344 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5350 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____5350 with
           | (lh,uu____5363) ->
               let uu____5378 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____5378 with
                | (rh,uu____5391) ->
                    let uu____5406 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5415,FStar_Syntax_Syntax.Tm_uvar uu____5416)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5435,uu____5436)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5447,FStar_Syntax_Syntax.Tm_uvar uu____5448)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5459,uu____5460)
                          ->
                          let uu____5469 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5469 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5509 ->
                                    let rank =
                                      let uu____5516 = is_top_level_prob prob in
                                      if uu____5516
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5518 =
                                      let uu___149_5521 = tp in
                                      let uu____5524 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_5521.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___149_5521.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_5521.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5524;
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_5521.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_5521.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_5521.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_5521.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_5521.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_5521.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5518)))
                      | (uu____5534,FStar_Syntax_Syntax.Tm_uvar uu____5535)
                          ->
                          let uu____5544 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5544 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5584 ->
                                    let uu____5590 =
                                      let uu___150_5595 = tp in
                                      let uu____5598 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___150_5595.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5598;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___150_5595.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___150_5595.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___150_5595.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___150_5595.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___150_5595.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___150_5595.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___150_5595.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___150_5595.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5590)))
                      | (uu____5614,uu____5615) -> (rigid_rigid, tp) in
                    (match uu____5406 with
                     | (rank,tp1) ->
                         let uu____5626 =
                           FStar_All.pipe_right
                             (let uu___151_5629 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___151_5629.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___151_5629.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___151_5629.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___151_5629.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___151_5629.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___151_5629.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___151_5629.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___151_5629.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___151_5629.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_43  ->
                                FStar_TypeChecker_Common.TProb _0_43) in
                         (rank, uu____5626))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5635 =
            FStar_All.pipe_right
              (let uu___152_5638 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___152_5638.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___152_5638.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___152_5638.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___152_5638.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___152_5638.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___152_5638.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___152_5638.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___152_5638.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___152_5638.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) in
          (rigid_rigid, uu____5635)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob option* FStar_TypeChecker_Common.prob
      Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____5670 probs =
      match uu____5670 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5700 = rank wl hd1 in
               (match uu____5700 with
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
    match projectee with | UDeferred _0 -> true | uu____5768 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5780 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5792 -> false
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
                        let uu____5825 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____5825 with
                        | (k,uu____5829) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____5833 -> false)))
            | uu____5834 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____5877 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____5877 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5880 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____5886 =
                     let uu____5887 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____5888 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5887
                       uu____5888 in
                   UFailed uu____5886)
            | (FStar_Syntax_Syntax.U_max us,u') ->
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
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5922 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5922 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____5925 ->
                let uu____5928 =
                  let uu____5929 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____5930 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5929
                    uu____5930 msg in
                UFailed uu____5928 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____5931,uu____5932) ->
              let uu____5933 =
                let uu____5934 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5935 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5934 uu____5935 in
              failwith uu____5933
          | (FStar_Syntax_Syntax.U_unknown ,uu____5936) ->
              let uu____5937 =
                let uu____5938 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5939 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5938 uu____5939 in
              failwith uu____5937
          | (uu____5940,FStar_Syntax_Syntax.U_bvar uu____5941) ->
              let uu____5942 =
                let uu____5943 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5944 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5943 uu____5944 in
              failwith uu____5942
          | (uu____5945,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____5946 =
                let uu____5947 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5948 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5947 uu____5948 in
              failwith uu____5946
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____5960 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____5960
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____5970 = occurs_univ v1 u3 in
              if uu____5970
              then
                let uu____5971 =
                  let uu____5972 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____5973 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5972 uu____5973 in
                try_umax_components u11 u21 uu____5971
              else
                (let uu____5975 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____5975)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____5983 = occurs_univ v1 u3 in
              if uu____5983
              then
                let uu____5984 =
                  let uu____5985 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____5986 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5985 uu____5986 in
                try_umax_components u11 u21 uu____5984
              else
                (let uu____5988 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____5988)
          | (FStar_Syntax_Syntax.U_max uu____5991,uu____5992) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____5997 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____5997
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____5999,FStar_Syntax_Syntax.U_max uu____6000) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6005 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6005
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6007,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6008,FStar_Syntax_Syntax.U_name
             uu____6009) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6010) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6011) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6012,FStar_Syntax_Syntax.U_succ
             uu____6013) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6014,FStar_Syntax_Syntax.U_zero
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
  let uu____6076 = bc1 in
  match uu____6076 with
  | (bs1,mk_cod1) ->
      let uu____6101 = bc2 in
      (match uu____6101 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6148 = FStar_Util.first_N n1 bs in
             match uu____6148 with
             | (bs3,rest) ->
                 let uu____6162 = mk_cod rest in (bs3, uu____6162) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____6180 =
               let uu____6184 = mk_cod1 [] in (bs1, uu____6184) in
             let uu____6186 =
               let uu____6190 = mk_cod2 [] in (bs2, uu____6190) in
             (uu____6180, uu____6186)
           else
             if l1 > l2
             then
               (let uu____6212 = curry l2 bs1 mk_cod1 in
                let uu____6219 =
                  let uu____6223 = mk_cod2 [] in (bs2, uu____6223) in
                (uu____6212, uu____6219))
             else
               (let uu____6232 =
                  let uu____6236 = mk_cod1 [] in (bs1, uu____6236) in
                let uu____6238 = curry l1 bs2 mk_cod2 in
                (uu____6232, uu____6238)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6342 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____6342
       then
         let uu____6343 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6343
       else ());
      (let uu____6345 = next_prob probs in
       match uu____6345 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___153_6358 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___153_6358.wl_deferred);
               ctr = (uu___153_6358.ctr);
               defer_ok = (uu___153_6358.defer_ok);
               smt_ok = (uu___153_6358.smt_ok);
               tcenv = (uu___153_6358.tcenv)
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
                  let uu____6365 = solve_flex_rigid_join env tp probs1 in
                  (match uu____6365 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6369 = solve_rigid_flex_meet env tp probs1 in
                     match uu____6369 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____6373,uu____6374) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6383 ->
                let uu____6388 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6416  ->
                          match uu____6416 with
                          | (c,uu____6421,uu____6422) -> c < probs.ctr)) in
                (match uu____6388 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6444 =
                            FStar_List.map
                              (fun uu____6450  ->
                                 match uu____6450 with
                                 | (uu____6456,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____6444
                      | uu____6459 ->
                          let uu____6464 =
                            let uu___154_6465 = probs in
                            let uu____6466 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6475  ->
                                      match uu____6475 with
                                      | (uu____6479,uu____6480,y) -> y)) in
                            {
                              attempting = uu____6466;
                              wl_deferred = rest;
                              ctr = (uu___154_6465.ctr);
                              defer_ok = (uu___154_6465.defer_ok);
                              smt_ok = (uu___154_6465.smt_ok);
                              tcenv = (uu___154_6465.tcenv)
                            } in
                          solve env uu____6464))))
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
            let uu____6487 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____6487 with
            | USolved wl1 ->
                let uu____6489 = solve_prob orig None [] wl1 in
                solve env uu____6489
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
                  let uu____6523 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6523 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6526 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6534;
                  FStar_Syntax_Syntax.pos = uu____6535;
                  FStar_Syntax_Syntax.vars = uu____6536;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6539;
                  FStar_Syntax_Syntax.pos = uu____6540;
                  FStar_Syntax_Syntax.vars = uu____6541;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6553,uu____6554) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6559,FStar_Syntax_Syntax.Tm_uinst uu____6560) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6565 -> USolved wl
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
            ((let uu____6573 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6573
              then
                let uu____6574 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6574 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6582 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6582
         then
           let uu____6583 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6583
         else ());
        (let uu____6585 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6585 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6627 = head_matches_delta env () t1 t2 in
               match uu____6627 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6649 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6675 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6684 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____6685 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____6684, uu____6685)
                          | None  ->
                              let uu____6688 = FStar_Syntax_Subst.compress t1 in
                              let uu____6689 = FStar_Syntax_Subst.compress t2 in
                              (uu____6688, uu____6689) in
                        (match uu____6675 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6711 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_45  ->
                                    FStar_TypeChecker_Common.TProb _0_45)
                                 uu____6711 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6734 =
                                    let uu____6740 =
                                      let uu____6743 =
                                        let uu____6746 =
                                          let uu____6747 =
                                            let uu____6752 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____6752) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6747 in
                                        FStar_Syntax_Syntax.mk uu____6746 in
                                      uu____6743 None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____6765 =
                                      let uu____6767 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____6767] in
                                    (uu____6740, uu____6765) in
                                  Some uu____6734
                              | (uu____6776,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6778)) ->
                                  let uu____6783 =
                                    let uu____6787 =
                                      let uu____6789 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____6789] in
                                    (t11, uu____6787) in
                                  Some uu____6783
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6795),uu____6796) ->
                                  let uu____6801 =
                                    let uu____6805 =
                                      let uu____6807 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____6807] in
                                    (t21, uu____6805) in
                                  Some uu____6801
                              | uu____6812 ->
                                  let uu____6815 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____6815 with
                                   | (head1,uu____6830) ->
                                       let uu____6845 =
                                         let uu____6846 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____6846.FStar_Syntax_Syntax.n in
                                       (match uu____6845 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6853;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6855;_}
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
                                        | uu____6864 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6873) ->
                  let uu____6886 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___128_6895  ->
                            match uu___128_6895 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6900 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____6900 with
                                      | (u',uu____6911) ->
                                          let uu____6926 =
                                            let uu____6927 = whnf env u' in
                                            uu____6927.FStar_Syntax_Syntax.n in
                                          (match uu____6926 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____6931) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____6944 -> false))
                                 | uu____6945 -> false)
                            | uu____6947 -> false)) in
                  (match uu____6886 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____6968 tps =
                         match uu____6968 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____6995 =
                                    let uu____7000 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____7000 in
                                  (match uu____6995 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____7019 -> None) in
                       let uu____7024 =
                         let uu____7029 =
                           let uu____7033 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____7033, []) in
                         make_lower_bound uu____7029 lower_bounds in
                       (match uu____7024 with
                        | None  ->
                            ((let uu____7040 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7040
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
                            ((let uu____7053 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7053
                              then
                                let wl' =
                                  let uu___155_7055 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___155_7055.wl_deferred);
                                    ctr = (uu___155_7055.ctr);
                                    defer_ok = (uu___155_7055.defer_ok);
                                    smt_ok = (uu___155_7055.smt_ok);
                                    tcenv = (uu___155_7055.tcenv)
                                  } in
                                let uu____7056 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7056
                              else ());
                             (let uu____7058 =
                                solve_t env eq_prob
                                  (let uu___156_7059 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___156_7059.wl_deferred);
                                     ctr = (uu___156_7059.ctr);
                                     defer_ok = (uu___156_7059.defer_ok);
                                     smt_ok = (uu___156_7059.smt_ok);
                                     tcenv = (uu___156_7059.tcenv)
                                   }) in
                              match uu____7058 with
                              | Success uu____7061 ->
                                  let wl1 =
                                    let uu___157_7063 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___157_7063.wl_deferred);
                                      ctr = (uu___157_7063.ctr);
                                      defer_ok = (uu___157_7063.defer_ok);
                                      smt_ok = (uu___157_7063.smt_ok);
                                      tcenv = (uu___157_7063.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1 in
                                  let uu____7065 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds in
                                  Some wl2
                              | uu____7068 -> None))))
              | uu____7069 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7076 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____7076
         then
           let uu____7077 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7077
         else ());
        (let uu____7079 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____7079 with
         | (u,args) ->
             let uu____7106 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____7106 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____7137 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____7137 with
                    | (h1,args1) ->
                        let uu____7165 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____7165 with
                         | (h2,uu____7178) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7197 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____7197
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7210 =
                                          let uu____7212 =
                                            let uu____7213 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_46  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_46) uu____7213 in
                                          [uu____7212] in
                                        Some uu____7210))
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
                                       (let uu____7235 =
                                          let uu____7237 =
                                            let uu____7238 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_47  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_47) uu____7238 in
                                          [uu____7237] in
                                        Some uu____7235))
                                  else None
                              | uu____7246 -> None)) in
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
                             let uu____7312 =
                               let uu____7318 =
                                 let uu____7321 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____7321 in
                               (uu____7318, m1) in
                             Some uu____7312)
                    | (uu____7330,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7332)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7364),uu____7365) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____7396 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7430) ->
                       let uu____7443 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___129_7452  ->
                                 match uu___129_7452 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____7457 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____7457 with
                                           | (u',uu____7468) ->
                                               let uu____7483 =
                                                 let uu____7484 = whnf env u' in
                                                 uu____7484.FStar_Syntax_Syntax.n in
                                               (match uu____7483 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7488) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____7501 -> false))
                                      | uu____7502 -> false)
                                 | uu____7504 -> false)) in
                       (match uu____7443 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7529 tps =
                              match uu____7529 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7570 =
                                         let uu____7577 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7577 in
                                       (match uu____7570 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7612 -> None) in
                            let uu____7619 =
                              let uu____7626 =
                                let uu____7632 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7632, []) in
                              make_upper_bound uu____7626 upper_bounds in
                            (match uu____7619 with
                             | None  ->
                                 ((let uu____7641 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7641
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
                                 ((let uu____7660 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7660
                                   then
                                     let wl' =
                                       let uu___158_7662 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___158_7662.wl_deferred);
                                         ctr = (uu___158_7662.ctr);
                                         defer_ok = (uu___158_7662.defer_ok);
                                         smt_ok = (uu___158_7662.smt_ok);
                                         tcenv = (uu___158_7662.tcenv)
                                       } in
                                     let uu____7663 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7663
                                   else ());
                                  (let uu____7665 =
                                     solve_t env eq_prob
                                       (let uu___159_7666 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___159_7666.wl_deferred);
                                          ctr = (uu___159_7666.ctr);
                                          defer_ok = (uu___159_7666.defer_ok);
                                          smt_ok = (uu___159_7666.smt_ok);
                                          tcenv = (uu___159_7666.tcenv)
                                        }) in
                                   match uu____7665 with
                                   | Success uu____7668 ->
                                       let wl1 =
                                         let uu___160_7670 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___160_7670.wl_deferred);
                                           ctr = (uu___160_7670.ctr);
                                           defer_ok =
                                             (uu___160_7670.defer_ok);
                                           smt_ok = (uu___160_7670.smt_ok);
                                           tcenv = (uu___160_7670.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1 in
                                       let uu____7672 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds in
                                       Some wl2
                                   | uu____7675 -> None))))
                   | uu____7676 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____7741 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____7741
                      then
                        let uu____7742 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7742
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___161_7774 = hd1 in
                      let uu____7775 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_7774.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_7774.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7775
                      } in
                    let hd21 =
                      let uu___162_7779 = hd2 in
                      let uu____7780 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___162_7779.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___162_7779.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7780
                      } in
                    let prob =
                      let uu____7784 =
                        let uu____7787 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7787 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_48  -> FStar_TypeChecker_Common.TProb _0_48)
                        uu____7784 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____7795 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7795 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____7798 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____7798 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7816 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives.fst in
                           let uu____7819 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____7816 uu____7819 in
                         ((let uu____7825 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____7825
                           then
                             let uu____7826 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____7827 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7826 uu____7827
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7842 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____7848 = aux scope env [] bs1 bs2 in
              match uu____7848 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7864 = compress_tprob wl problem in
        solve_t' env uu____7864 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7897 = head_matches_delta env1 wl1 t1 t2 in
          match uu____7897 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7914,uu____7915) ->
                   let may_relate head3 =
                     let uu____7930 =
                       let uu____7931 = FStar_Syntax_Util.un_uinst head3 in
                       uu____7931.FStar_Syntax_Syntax.n in
                     match uu____7930 with
                     | FStar_Syntax_Syntax.Tm_name uu____7934 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____7935 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____7952 -> false in
                   let uu____7953 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____7953
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
                                let uu____7970 =
                                  let uu____7971 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____7971 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____7970 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____7973 = solve_prob orig (Some guard) [] wl1 in
                     solve env1 uu____7973
                   else
                     (let uu____7975 =
                        let uu____7976 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____7977 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____7976 uu____7977 in
                      giveup env1 uu____7975 orig)
               | (uu____7978,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___163_7986 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___163_7986.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___163_7986.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___163_7986.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___163_7986.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___163_7986.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___163_7986.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___163_7986.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___163_7986.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____7987,None ) ->
                   ((let uu____7994 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____7994
                     then
                       let uu____7995 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____7996 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____7997 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____7998 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____7995
                         uu____7996 uu____7997 uu____7998
                     else ());
                    (let uu____8000 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____8000 with
                     | (head11,args1) ->
                         let uu____8026 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____8026 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8066 =
                                  let uu____8067 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____8068 = args_to_string args1 in
                                  let uu____8069 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____8070 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8067 uu____8068 uu____8069
                                    uu____8070 in
                                giveup env1 uu____8066 orig
                              else
                                (let uu____8072 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8075 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____8075 = FStar_Syntax_Util.Equal) in
                                 if uu____8072
                                 then
                                   let uu____8076 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____8076 with
                                   | USolved wl2 ->
                                       let uu____8078 =
                                         solve_prob orig None [] wl2 in
                                       solve env1 uu____8078
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8082 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____8082 with
                                    | (base1,refinement1) ->
                                        let uu____8108 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____8108 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____8162 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____8162 with
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
                                                           (fun uu____8172 
                                                              ->
                                                              fun uu____8173 
                                                                ->
                                                                match 
                                                                  (uu____8172,
                                                                    uu____8173)
                                                                with
                                                                | ((a,uu____8183),
                                                                   (a',uu____8185))
                                                                    ->
                                                                    let uu____8190
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
                                                                    uu____8190)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____8196 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8196 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8200 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___164_8233 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___164_8233.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___164_8233.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___164_8233.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___164_8233.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___164_8233.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___164_8233.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___164_8233.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___164_8233.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____8253 = p in
          match uu____8253 with
          | (((u,k),xs,c),ps,(h,uu____8264,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8313 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____8313 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8327 = h gs_xs in
                     let uu____8328 =
                       let uu____8335 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_50  -> FStar_Util.Inl _0_50) in
                       FStar_All.pipe_right uu____8335
                         (fun _0_51  -> Some _0_51) in
                     FStar_Syntax_Util.abs xs1 uu____8327 uu____8328 in
                   ((let uu____8366 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8366
                     then
                       let uu____8367 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____8368 = FStar_Syntax_Print.comp_to_string c in
                       let uu____8369 = FStar_Syntax_Print.term_to_string im in
                       let uu____8370 = FStar_Syntax_Print.tag_of_term im in
                       let uu____8371 =
                         let uu____8372 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____8372
                           (FStar_String.concat ", ") in
                       let uu____8375 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8367 uu____8368 uu____8369 uu____8370
                         uu____8371 uu____8375
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___130_8393 =
          match uu___130_8393 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____8422 = p in
          match uu____8422 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8480 = FStar_List.nth ps i in
              (match uu____8480 with
               | (pi,uu____8483) ->
                   let uu____8488 = FStar_List.nth xs i in
                   (match uu____8488 with
                    | (xi,uu____8495) ->
                        let rec gs k =
                          let uu____8504 = FStar_Syntax_Util.arrow_formals k in
                          match uu____8504 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8556)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8564 = new_uvar r xs k_a in
                                    (match uu____8564 with
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
                                         let uu____8583 = aux subst2 tl1 in
                                         (match uu____8583 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8598 =
                                                let uu____8600 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8600 :: gi_xs' in
                                              let uu____8601 =
                                                let uu____8603 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8603 :: gi_ps' in
                                              (uu____8598, uu____8601))) in
                              aux [] bs in
                        let uu____8606 =
                          let uu____8607 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8607 in
                        if uu____8606
                        then None
                        else
                          (let uu____8610 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8610 with
                           | (g_xs,uu____8617) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8624 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r in
                                 let uu____8629 =
                                   let uu____8636 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_52  -> FStar_Util.Inl _0_52) in
                                   FStar_All.pipe_right uu____8636
                                     (fun _0_53  -> Some _0_53) in
                                 FStar_Syntax_Util.abs xs uu____8624
                                   uu____8629 in
                               let sub1 =
                                 let uu____8667 =
                                   let uu____8670 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let uu____8677 =
                                     let uu____8680 =
                                       FStar_List.map
                                         (fun uu____8686  ->
                                            match uu____8686 with
                                            | (uu____8691,uu____8692,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____8680 in
                                   mk_problem (p_scope orig) orig uu____8670
                                     (p_rel orig) uu____8677 None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_54  ->
                                      FStar_TypeChecker_Common.TProb _0_54)
                                   uu____8667 in
                               ((let uu____8702 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____8702
                                 then
                                   let uu____8703 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____8704 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8703 uu____8704
                                 else ());
                                (let wl2 =
                                   let uu____8707 =
                                     let uu____8709 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives.fst (p_guard sub1) in
                                     Some uu____8709 in
                                   solve_prob orig uu____8707
                                     [TERM (u, proj)] wl1 in
                                 let uu____8714 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_55  -> Some _0_55) uu____8714))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8738 = lhs in
          match uu____8738 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8761 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____8761 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8783 =
                        let uu____8809 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____8809) in
                      Some uu____8783
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____8892 =
                           let uu____8896 =
                             let uu____8897 = FStar_Syntax_Subst.compress k in
                             uu____8897.FStar_Syntax_Syntax.n in
                           (uu____8896, args) in
                         match uu____8892 with
                         | (uu____8904,[]) ->
                             let uu____8906 =
                               let uu____8912 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____8912) in
                             Some uu____8906
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____8923,uu____8924) ->
                             let uu____8935 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____8935 with
                              | (uv1,uv_args) ->
                                  let uu____8964 =
                                    let uu____8965 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____8965.FStar_Syntax_Syntax.n in
                                  (match uu____8964 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____8972) ->
                                       let uu____8985 =
                                         pat_vars env [] uv_args in
                                       (match uu____8985 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____8999  ->
                                                      let uu____9000 =
                                                        let uu____9001 =
                                                          let uu____9002 =
                                                            let uu____9005 =
                                                              let uu____9006
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9006
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9005 in
                                                          fst uu____9002 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9001 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9000)) in
                                            let c1 =
                                              let uu____9012 =
                                                let uu____9013 =
                                                  let uu____9016 =
                                                    let uu____9017 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9017
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9016 in
                                                fst uu____9013 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9012 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9026 =
                                                let uu____9033 =
                                                  let uu____9039 =
                                                    let uu____9040 =
                                                      let uu____9043 =
                                                        let uu____9044 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9044
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9043 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9040 in
                                                  FStar_Util.Inl uu____9039 in
                                                Some uu____9033 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9026 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9064 -> None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9067,uu____9068)
                             ->
                             let uu____9080 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9080 with
                              | (uv1,uv_args) ->
                                  let uu____9109 =
                                    let uu____9110 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9110.FStar_Syntax_Syntax.n in
                                  (match uu____9109 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9117) ->
                                       let uu____9130 =
                                         pat_vars env [] uv_args in
                                       (match uu____9130 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9144  ->
                                                      let uu____9145 =
                                                        let uu____9146 =
                                                          let uu____9147 =
                                                            let uu____9150 =
                                                              let uu____9151
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9151
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9150 in
                                                          fst uu____9147 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9146 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9145)) in
                                            let c1 =
                                              let uu____9157 =
                                                let uu____9158 =
                                                  let uu____9161 =
                                                    let uu____9162 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9162
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9161 in
                                                fst uu____9158 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9157 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9171 =
                                                let uu____9178 =
                                                  let uu____9184 =
                                                    let uu____9185 =
                                                      let uu____9188 =
                                                        let uu____9189 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9189
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9188 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9185 in
                                                  FStar_Util.Inl uu____9184 in
                                                Some uu____9178 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9171 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9209 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9214)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____9240 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____9240
                                 (fun _0_56  -> Some _0_56)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9259 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____9259 with
                                  | (args1,rest) ->
                                      let uu____9275 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____9275 with
                                       | (xs2,c2) ->
                                           let uu____9283 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____9283
                                             (fun uu____9294  ->
                                                match uu____9294 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9316 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____9316 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____9362 =
                                        let uu____9365 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9365 in
                                      FStar_All.pipe_right uu____9362
                                        (fun _0_57  -> Some _0_57))
                         | uu____9373 ->
                             let uu____9377 =
                               let uu____9378 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____9379 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____9380 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9378 uu____9379 uu____9380 in
                             failwith uu____9377 in
                       let uu____9384 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____9384
                         (fun uu____9412  ->
                            match uu____9412 with
                            | (xs1,c1) ->
                                let uu____9440 =
                                  let uu____9463 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9463) in
                                Some uu____9440)) in
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
                     let uu____9535 = imitate orig env wl1 st in
                     match uu____9535 with
                     | Failed uu____9540 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9546 = project orig env wl1 i st in
                      match uu____9546 with
                      | None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some (Failed uu____9553) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____9567 = FStar_Syntax_Util.head_and_args t21 in
                match uu____9567 with
                | (hd1,uu____9578) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9593 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9601 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9602 -> true
                     | uu____9617 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____9620 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____9620
                         then true
                         else
                           ((let uu____9623 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____9623
                             then
                               let uu____9624 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9624
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9632 =
                    let uu____9635 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____9635 FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____9632 FStar_Syntax_Free.names in
                let uu____9666 = FStar_Util.set_is_empty fvs_hd in
                if uu____9666
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____9675 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____9675 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9683 =
                            let uu____9684 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____9684 in
                          giveup_or_defer1 orig uu____9683
                        else
                          (let uu____9686 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____9686
                           then
                             let uu____9687 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____9687
                              then
                                let uu____9688 = subterms args_lhs in
                                imitate' orig env wl1 uu____9688
                              else
                                ((let uu____9692 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____9692
                                  then
                                    let uu____9693 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____9694 = names_to_string fvs1 in
                                    let uu____9695 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9693 uu____9694 uu____9695
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9700 ->
                                        let uu____9701 = sn_binders env vars in
                                        u_abs k_uv uu____9701 t21 in
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
                               (let uu____9710 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____9710
                                then
                                  ((let uu____9712 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____9712
                                    then
                                      let uu____9713 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____9714 = names_to_string fvs1 in
                                      let uu____9715 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9713 uu____9714 uu____9715
                                    else ());
                                   (let uu____9717 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9717
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
                     (let uu____9728 =
                        let uu____9729 = FStar_Syntax_Free.names t1 in
                        check_head uu____9729 t2 in
                      if uu____9728
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____9733 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____9733
                          then
                            let uu____9734 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9734
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9737 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9737 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9779 =
               match uu____9779 with
               | (t,u,k,args) ->
                   let uu____9809 = FStar_Syntax_Util.arrow_formals k in
                   (match uu____9809 with
                    | (all_formals,uu____9820) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____9912  ->
                                        match uu____9912 with
                                        | (x,imp) ->
                                            let uu____9919 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____9919, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____9927 = FStar_Syntax_Util.type_u () in
                                match uu____9927 with
                                | (t1,uu____9931) ->
                                    let uu____9932 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    fst uu____9932 in
                              let uu____9935 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____9935 with
                               | (t',tm_u1) ->
                                   let uu____9942 = destruct_flex_t t' in
                                   (match uu____9942 with
                                    | (uu____9962,u1,k1,uu____9965) ->
                                        let sol =
                                          let uu____9993 =
                                            let uu____9998 =
                                              u_abs k all_formals t' in
                                            ((u, k), uu____9998) in
                                          TERM uu____9993 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k1, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10058 = pat_var_opt env pat_args hd1 in
                              (match uu____10058 with
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
                                              (fun uu____10087  ->
                                                 match uu____10087 with
                                                 | (x,uu____10091) ->
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
                                      let uu____10097 =
                                        let uu____10098 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____10098 in
                                      if uu____10097
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10102 =
                                           FStar_Util.set_add (fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10102 formals1
                                           tl1)))
                          | uu____10108 -> failwith "Impossible" in
                        let uu____10119 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____10119 all_formals args) in
             let solve_both_pats wl1 uu____10159 uu____10160 r =
               match (uu____10159, uu____10160) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10274 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____10274
                   then
                     let uu____10275 = solve_prob orig None [] wl1 in
                     solve env uu____10275
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____10290 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____10290
                       then
                         let uu____10291 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____10292 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____10293 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____10294 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____10295 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10291 uu____10292 uu____10293 uu____10294
                           uu____10295
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____10337 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____10337 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10345 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____10345 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10375 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10375 in
                                  let uu____10378 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____10378 k3)
                           else
                             (let uu____10381 =
                                let uu____10382 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____10383 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____10384 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10382 uu____10383 uu____10384 in
                              failwith uu____10381) in
                       let uu____10385 =
                         let uu____10391 =
                           let uu____10399 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____10399 in
                         match uu____10391 with
                         | (bs,k1') ->
                             let uu____10417 =
                               let uu____10425 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____10425 in
                             (match uu____10417 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____10446 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_58  ->
                                         FStar_TypeChecker_Common.TProb _0_58)
                                      uu____10446 in
                                  let uu____10451 =
                                    let uu____10454 =
                                      let uu____10455 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____10455.FStar_Syntax_Syntax.n in
                                    let uu____10458 =
                                      let uu____10459 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____10459.FStar_Syntax_Syntax.n in
                                    (uu____10454, uu____10458) in
                                  (match uu____10451 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10467,uu____10468) ->
                                       (k1', [sub_prob])
                                   | (uu____10472,FStar_Syntax_Syntax.Tm_type
                                      uu____10473) -> (k2', [sub_prob])
                                   | uu____10477 ->
                                       let uu____10480 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____10480 with
                                        | (t,uu____10489) ->
                                            let uu____10490 = new_uvar r zs t in
                                            (match uu____10490 with
                                             | (k_zs,uu____10499) ->
                                                 let kprob =
                                                   let uu____10501 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_59  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_59) uu____10501 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____10385 with
                       | (k_u',sub_probs) ->
                           let uu____10515 =
                             let uu____10523 =
                               let uu____10524 = new_uvar r zs k_u' in
                               FStar_All.pipe_left FStar_Pervasives.fst
                                 uu____10524 in
                             let uu____10529 =
                               let uu____10532 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____10532 in
                             let uu____10535 =
                               let uu____10538 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____10538 in
                             (uu____10523, uu____10529, uu____10535) in
                           (match uu____10515 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____10557 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____10557 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____10569 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____10569
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____10573 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____10573 with
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
             let solve_one_pat uu____10605 uu____10606 =
               match (uu____10605, uu____10606) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10670 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____10670
                     then
                       let uu____10671 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10672 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10671 uu____10672
                     else ());
                    (let uu____10674 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____10674
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10681  ->
                              fun uu____10682  ->
                                match (uu____10681, uu____10682) with
                                | ((a,uu____10692),(t21,uu____10694)) ->
                                    let uu____10699 =
                                      let uu____10702 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____10702
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____10699
                                      (fun _0_60  ->
                                         FStar_TypeChecker_Common.TProb _0_60))
                           xs args2 in
                       let guard =
                         let uu____10706 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____10706 in
                       let wl1 = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____10716 = occurs_check env wl (u1, k1) t21 in
                        match uu____10716 with
                        | (occurs_ok,uu____10721) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____10726 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____10726
                            then
                              let sol =
                                let uu____10728 =
                                  let uu____10733 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____10733) in
                                TERM uu____10728 in
                              let wl1 = solve_prob orig None [sol] wl in
                              solve env wl1
                            else
                              (let uu____10738 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____10738
                               then
                                 let uu____10739 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____10739 with
                                 | (sol,(uu____10749,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____10759 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____10759
                                       then
                                         let uu____10760 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10760
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10765 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____10767 = lhs in
             match uu____10767 with
             | (t1,u1,k1,args1) ->
                 let uu____10772 = rhs in
                 (match uu____10772 with
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
                       | uu____10798 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____10804 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____10804 with
                              | (sol,uu____10811) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____10814 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____10814
                                    then
                                      let uu____10815 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____10815
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____10820 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____10822 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____10822
        then
          let uu____10823 = solve_prob orig None [] wl in
          solve env uu____10823
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____10827 = FStar_Util.physical_equality t1 t2 in
           if uu____10827
           then
             let uu____10828 = solve_prob orig None [] wl in
             solve env uu____10828
           else
             ((let uu____10831 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____10831
               then
                 let uu____10832 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____10832
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____10835,uu____10836) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____10837,FStar_Syntax_Syntax.Tm_bvar uu____10838) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___131_10878 =
                     match uu___131_10878 with
                     | [] -> c
                     | bs ->
                         let uu____10892 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c)) None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____10892 in
                   let uu____10902 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____10902 with
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
                                   let uu____10988 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____10988
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____10990 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.CProb _0_61)
                                   uu____10990))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___132_11067 =
                     match uu___132_11067 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l)) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____11102 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____11102 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11185 =
                                   let uu____11188 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____11189 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____11188
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11189 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_TypeChecker_Common.TProb _0_62)
                                   uu____11185))
               | (FStar_Syntax_Syntax.Tm_abs uu____11192,uu____11193) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11216 -> true
                     | uu____11231 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11259 =
                     let uu____11270 = maybe_eta t1 in
                     let uu____11275 = maybe_eta t2 in
                     (uu____11270, uu____11275) in
                   (match uu____11259 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___165_11306 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___165_11306.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___165_11306.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___165_11306.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___165_11306.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___165_11306.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___165_11306.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___165_11306.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___165_11306.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11325 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11325
                        then
                          let uu____11326 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11326 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11347 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11347
                        then
                          let uu____11348 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11348 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11353 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11364,FStar_Syntax_Syntax.Tm_abs uu____11365) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11388 -> true
                     | uu____11403 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11431 =
                     let uu____11442 = maybe_eta t1 in
                     let uu____11447 = maybe_eta t2 in
                     (uu____11442, uu____11447) in
                   (match uu____11431 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___165_11478 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___165_11478.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___165_11478.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___165_11478.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___165_11478.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___165_11478.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___165_11478.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___165_11478.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___165_11478.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11497 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11497
                        then
                          let uu____11498 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11498 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11519 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11519
                        then
                          let uu____11520 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11520 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11525 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11536,FStar_Syntax_Syntax.Tm_refine uu____11537) ->
                   let uu____11546 = as_refinement env wl t1 in
                   (match uu____11546 with
                    | (x1,phi1) ->
                        let uu____11551 = as_refinement env wl t2 in
                        (match uu____11551 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11557 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_63  ->
                                    FStar_TypeChecker_Common.TProb _0_63)
                                 uu____11557 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____11590 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____11590
                                 (guard_on_element wl problem x11) in
                             let fallback uu____11594 =
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
                                 let uu____11600 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____11600 impl in
                               let wl1 = solve_prob orig (Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11607 =
                                   let uu____11610 =
                                     let uu____11611 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____11611 :: (p_scope orig) in
                                   mk_problem uu____11610 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____11607 in
                               let uu____11614 =
                                 solve env1
                                   (let uu___166_11615 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___166_11615.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___166_11615.smt_ok);
                                      tcenv = (uu___166_11615.tcenv)
                                    }) in
                               (match uu____11614 with
                                | Failed uu____11619 -> fallback ()
                                | Success uu____11622 ->
                                    let guard =
                                      let uu____11626 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives.fst in
                                      let uu____11629 =
                                        let uu____11630 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives.fst in
                                        FStar_All.pipe_right uu____11630
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____11626
                                        uu____11629 in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl2 =
                                      let uu___167_11637 = wl1 in
                                      {
                                        attempting =
                                          (uu___167_11637.attempting);
                                        wl_deferred =
                                          (uu___167_11637.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___167_11637.defer_ok);
                                        smt_ok = (uu___167_11637.smt_ok);
                                        tcenv = (uu___167_11637.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11639,FStar_Syntax_Syntax.Tm_uvar uu____11640) ->
                   let uu____11657 = destruct_flex_t t1 in
                   let uu____11658 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11657 uu____11658
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11659;
                     FStar_Syntax_Syntax.tk = uu____11660;
                     FStar_Syntax_Syntax.pos = uu____11661;
                     FStar_Syntax_Syntax.vars = uu____11662;_},uu____11663),FStar_Syntax_Syntax.Tm_uvar
                  uu____11664) ->
                   let uu____11695 = destruct_flex_t t1 in
                   let uu____11696 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11695 uu____11696
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11697,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11698;
                     FStar_Syntax_Syntax.tk = uu____11699;
                     FStar_Syntax_Syntax.pos = uu____11700;
                     FStar_Syntax_Syntax.vars = uu____11701;_},uu____11702))
                   ->
                   let uu____11733 = destruct_flex_t t1 in
                   let uu____11734 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11733 uu____11734
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11735;
                     FStar_Syntax_Syntax.tk = uu____11736;
                     FStar_Syntax_Syntax.pos = uu____11737;
                     FStar_Syntax_Syntax.vars = uu____11738;_},uu____11739),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11740;
                     FStar_Syntax_Syntax.tk = uu____11741;
                     FStar_Syntax_Syntax.pos = uu____11742;
                     FStar_Syntax_Syntax.vars = uu____11743;_},uu____11744))
                   ->
                   let uu____11789 = destruct_flex_t t1 in
                   let uu____11790 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11789 uu____11790
               | (FStar_Syntax_Syntax.Tm_uvar uu____11791,uu____11792) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11801 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11801 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11805;
                     FStar_Syntax_Syntax.tk = uu____11806;
                     FStar_Syntax_Syntax.pos = uu____11807;
                     FStar_Syntax_Syntax.vars = uu____11808;_},uu____11809),uu____11810)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11833 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11833 t2 wl
               | (uu____11837,FStar_Syntax_Syntax.Tm_uvar uu____11838) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____11847,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11848;
                     FStar_Syntax_Syntax.tk = uu____11849;
                     FStar_Syntax_Syntax.pos = uu____11850;
                     FStar_Syntax_Syntax.vars = uu____11851;_},uu____11852))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11875,FStar_Syntax_Syntax.Tm_type uu____11876) ->
                   solve_t' env
                     (let uu___168_11885 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_11885.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_11885.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_11885.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_11885.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_11885.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_11885.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_11885.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_11885.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_11885.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11886;
                     FStar_Syntax_Syntax.tk = uu____11887;
                     FStar_Syntax_Syntax.pos = uu____11888;
                     FStar_Syntax_Syntax.vars = uu____11889;_},uu____11890),FStar_Syntax_Syntax.Tm_type
                  uu____11891) ->
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
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11915,FStar_Syntax_Syntax.Tm_arrow uu____11916) ->
                   solve_t' env
                     (let uu___168_11932 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_11932.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_11932.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_11932.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_11932.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_11932.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_11932.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_11932.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_11932.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_11932.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11933;
                     FStar_Syntax_Syntax.tk = uu____11934;
                     FStar_Syntax_Syntax.pos = uu____11935;
                     FStar_Syntax_Syntax.vars = uu____11936;_},uu____11937),FStar_Syntax_Syntax.Tm_arrow
                  uu____11938) ->
                   solve_t' env
                     (let uu___168_11968 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_11968.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_11968.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_11968.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_11968.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_11968.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_11968.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_11968.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_11968.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_11968.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____11969,uu____11970) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____11981 =
                        let uu____11982 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____11982 in
                      if uu____11981
                      then
                        let uu____11983 =
                          FStar_All.pipe_left
                            (fun _0_65  ->
                               FStar_TypeChecker_Common.TProb _0_65)
                            (let uu___169_11986 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_11986.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_11986.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_11986.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_11986.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_11986.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___169_11986.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_11986.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_11986.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_11986.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____11987 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____11983 uu____11987 t2
                          wl
                      else
                        (let uu____11992 = base_and_refinement env wl t2 in
                         match uu____11992 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12022 =
                                    FStar_All.pipe_left
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66)
                                      (let uu___170_12025 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___170_12025.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___170_12025.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___170_12025.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___170_12025.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___170_12025.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___170_12025.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___170_12025.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___170_12025.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___170_12025.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12026 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12022
                                    uu____12026 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___171_12041 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___171_12041.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___171_12041.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12044 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67)
                                      uu____12044 in
                                  let guard =
                                    let uu____12052 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12052
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12058;
                     FStar_Syntax_Syntax.tk = uu____12059;
                     FStar_Syntax_Syntax.pos = uu____12060;
                     FStar_Syntax_Syntax.vars = uu____12061;_},uu____12062),uu____12063)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12088 =
                        let uu____12089 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12089 in
                      if uu____12088
                      then
                        let uu____12090 =
                          FStar_All.pipe_left
                            (fun _0_68  ->
                               FStar_TypeChecker_Common.TProb _0_68)
                            (let uu___169_12093 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_12093.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_12093.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_12093.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_12093.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_12093.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___169_12093.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_12093.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_12093.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_12093.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12094 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12090 uu____12094 t2
                          wl
                      else
                        (let uu____12099 = base_and_refinement env wl t2 in
                         match uu____12099 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12129 =
                                    FStar_All.pipe_left
                                      (fun _0_69  ->
                                         FStar_TypeChecker_Common.TProb _0_69)
                                      (let uu___170_12132 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___170_12132.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___170_12132.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___170_12132.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___170_12132.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___170_12132.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___170_12132.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___170_12132.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___170_12132.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___170_12132.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12133 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12129
                                    uu____12133 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___171_12148 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___171_12148.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___171_12148.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12151 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_70  ->
                                         FStar_TypeChecker_Common.TProb _0_70)
                                      uu____12151 in
                                  let guard =
                                    let uu____12159 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12159
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12165,FStar_Syntax_Syntax.Tm_uvar uu____12166) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12176 = base_and_refinement env wl t1 in
                      match uu____12176 with
                      | (t_base,uu____12187) ->
                          solve_t env
                            (let uu___172_12202 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___172_12202.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___172_12202.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___172_12202.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___172_12202.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___172_12202.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___172_12202.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___172_12202.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___172_12202.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12205,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12206;
                     FStar_Syntax_Syntax.tk = uu____12207;
                     FStar_Syntax_Syntax.pos = uu____12208;
                     FStar_Syntax_Syntax.vars = uu____12209;_},uu____12210))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12234 = base_and_refinement env wl t1 in
                      match uu____12234 with
                      | (t_base,uu____12245) ->
                          solve_t env
                            (let uu___172_12260 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___172_12260.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___172_12260.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___172_12260.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___172_12260.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___172_12260.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___172_12260.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___172_12260.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___172_12260.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12263,uu____12264) ->
                   let t21 =
                     let uu____12272 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____12272 in
                   solve_t env
                     (let uu___173_12285 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_12285.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___173_12285.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___173_12285.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___173_12285.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_12285.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_12285.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_12285.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_12285.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_12285.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12286,FStar_Syntax_Syntax.Tm_refine uu____12287) ->
                   let t11 =
                     let uu____12295 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____12295 in
                   solve_t env
                     (let uu___174_12308 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_12308.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___174_12308.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___174_12308.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___174_12308.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_12308.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_12308.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_12308.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_12308.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_12308.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12311,uu____12312) ->
                   let head1 =
                     let uu____12331 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12331 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12362 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12362 FStar_Pervasives.fst in
                   let uu____12390 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12390
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12399 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12399
                      then
                        let guard =
                          let uu____12406 =
                            let uu____12407 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12407 = FStar_Syntax_Util.Equal in
                          if uu____12406
                          then None
                          else
                            (let uu____12410 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_71  -> Some _0_71)
                               uu____12410) in
                        let uu____12412 = solve_prob orig guard [] wl in
                        solve env uu____12412
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12415,uu____12416) ->
                   let head1 =
                     let uu____12424 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12424 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12455 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12455 FStar_Pervasives.fst in
                   let uu____12483 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12483
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12492 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12492
                      then
                        let guard =
                          let uu____12499 =
                            let uu____12500 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12500 = FStar_Syntax_Util.Equal in
                          if uu____12499
                          then None
                          else
                            (let uu____12503 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_72  -> Some _0_72)
                               uu____12503) in
                        let uu____12505 = solve_prob orig guard [] wl in
                        solve env uu____12505
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12508,uu____12509) ->
                   let head1 =
                     let uu____12513 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12513 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12544 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12544 FStar_Pervasives.fst in
                   let uu____12572 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12572
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12581 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12581
                      then
                        let guard =
                          let uu____12588 =
                            let uu____12589 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12589 = FStar_Syntax_Util.Equal in
                          if uu____12588
                          then None
                          else
                            (let uu____12592 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_73  -> Some _0_73)
                               uu____12592) in
                        let uu____12594 = solve_prob orig guard [] wl in
                        solve env uu____12594
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12597,uu____12598) ->
                   let head1 =
                     let uu____12602 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12602 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12633 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12633 FStar_Pervasives.fst in
                   let uu____12661 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12661
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12670 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12670
                      then
                        let guard =
                          let uu____12677 =
                            let uu____12678 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12678 = FStar_Syntax_Util.Equal in
                          if uu____12677
                          then None
                          else
                            (let uu____12681 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_74  -> Some _0_74)
                               uu____12681) in
                        let uu____12683 = solve_prob orig guard [] wl in
                        solve env uu____12683
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____12686,uu____12687) ->
                   let head1 =
                     let uu____12691 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12691 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12722 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12722 FStar_Pervasives.fst in
                   let uu____12750 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12750
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12759 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12759
                      then
                        let guard =
                          let uu____12766 =
                            let uu____12767 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12767 = FStar_Syntax_Util.Equal in
                          if uu____12766
                          then None
                          else
                            (let uu____12770 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_75  -> Some _0_75)
                               uu____12770) in
                        let uu____12772 = solve_prob orig guard [] wl in
                        solve env uu____12772
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____12775,uu____12776) ->
                   let head1 =
                     let uu____12789 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12789 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12820 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12820 FStar_Pervasives.fst in
                   let uu____12848 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12848
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12857 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12857
                      then
                        let guard =
                          let uu____12864 =
                            let uu____12865 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12865 = FStar_Syntax_Util.Equal in
                          if uu____12864
                          then None
                          else
                            (let uu____12868 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_76  -> Some _0_76)
                               uu____12868) in
                        let uu____12870 = solve_prob orig guard [] wl in
                        solve env uu____12870
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12873,FStar_Syntax_Syntax.Tm_match uu____12874) ->
                   let head1 =
                     let uu____12893 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12893 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12924 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12924 FStar_Pervasives.fst in
                   let uu____12952 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12952
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12961 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12961
                      then
                        let guard =
                          let uu____12968 =
                            let uu____12969 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12969 = FStar_Syntax_Util.Equal in
                          if uu____12968
                          then None
                          else
                            (let uu____12972 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_77  -> Some _0_77)
                               uu____12972) in
                        let uu____12974 = solve_prob orig guard [] wl in
                        solve env uu____12974
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12977,FStar_Syntax_Syntax.Tm_uinst uu____12978) ->
                   let head1 =
                     let uu____12986 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12986 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13017 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13017 FStar_Pervasives.fst in
                   let uu____13045 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13045
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13054 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13054
                      then
                        let guard =
                          let uu____13061 =
                            let uu____13062 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13062 = FStar_Syntax_Util.Equal in
                          if uu____13061
                          then None
                          else
                            (let uu____13065 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_78  -> Some _0_78)
                               uu____13065) in
                        let uu____13067 = solve_prob orig guard [] wl in
                        solve env uu____13067
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13070,FStar_Syntax_Syntax.Tm_name uu____13071) ->
                   let head1 =
                     let uu____13075 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13075 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13106 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13106 FStar_Pervasives.fst in
                   let uu____13134 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13134
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13143 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13143
                      then
                        let guard =
                          let uu____13150 =
                            let uu____13151 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13151 = FStar_Syntax_Util.Equal in
                          if uu____13150
                          then None
                          else
                            (let uu____13154 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_79  -> Some _0_79)
                               uu____13154) in
                        let uu____13156 = solve_prob orig guard [] wl in
                        solve env uu____13156
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13159,FStar_Syntax_Syntax.Tm_constant uu____13160) ->
                   let head1 =
                     let uu____13164 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13164 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13195 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13195 FStar_Pervasives.fst in
                   let uu____13223 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13223
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13232 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13232
                      then
                        let guard =
                          let uu____13239 =
                            let uu____13240 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13240 = FStar_Syntax_Util.Equal in
                          if uu____13239
                          then None
                          else
                            (let uu____13243 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_80  -> Some _0_80)
                               uu____13243) in
                        let uu____13245 = solve_prob orig guard [] wl in
                        solve env uu____13245
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13248,FStar_Syntax_Syntax.Tm_fvar uu____13249) ->
                   let head1 =
                     let uu____13253 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13253 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13284 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13284 FStar_Pervasives.fst in
                   let uu____13312 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13312
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13321 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13321
                      then
                        let guard =
                          let uu____13328 =
                            let uu____13329 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13329 = FStar_Syntax_Util.Equal in
                          if uu____13328
                          then None
                          else
                            (let uu____13332 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_81  -> Some _0_81)
                               uu____13332) in
                        let uu____13334 = solve_prob orig guard [] wl in
                        solve env uu____13334
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13337,FStar_Syntax_Syntax.Tm_app uu____13338) ->
                   let head1 =
                     let uu____13351 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13351 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13382 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13382 FStar_Pervasives.fst in
                   let uu____13410 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13410
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13419 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13419
                      then
                        let guard =
                          let uu____13426 =
                            let uu____13427 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13427 = FStar_Syntax_Util.Equal in
                          if uu____13426
                          then None
                          else
                            (let uu____13430 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_82  -> Some _0_82)
                               uu____13430) in
                        let uu____13432 = solve_prob orig guard [] wl in
                        solve env uu____13432
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13436,uu____13437),uu____13438) ->
                   solve_t' env
                     (let uu___175_13467 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_13467.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_13467.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_13467.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_13467.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_13467.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_13467.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_13467.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_13467.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_13467.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13470,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13472,uu____13473)) ->
                   solve_t' env
                     (let uu___176_13502 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_13502.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___176_13502.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___176_13502.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___176_13502.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_13502.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_13502.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_13502.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_13502.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_13502.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13503,uu____13504) ->
                   let uu____13512 =
                     let uu____13513 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13514 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13513
                       uu____13514 in
                   failwith uu____13512
               | (FStar_Syntax_Syntax.Tm_meta uu____13515,uu____13516) ->
                   let uu____13521 =
                     let uu____13522 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13523 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13522
                       uu____13523 in
                   failwith uu____13521
               | (FStar_Syntax_Syntax.Tm_delayed uu____13524,uu____13525) ->
                   let uu____13546 =
                     let uu____13547 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13548 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13547
                       uu____13548 in
                   failwith uu____13546
               | (uu____13549,FStar_Syntax_Syntax.Tm_meta uu____13550) ->
                   let uu____13555 =
                     let uu____13556 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13557 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13556
                       uu____13557 in
                   failwith uu____13555
               | (uu____13558,FStar_Syntax_Syntax.Tm_delayed uu____13559) ->
                   let uu____13580 =
                     let uu____13581 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13582 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13581
                       uu____13582 in
                   failwith uu____13580
               | (uu____13583,FStar_Syntax_Syntax.Tm_let uu____13584) ->
                   let uu____13592 =
                     let uu____13593 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13594 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13593
                       uu____13594 in
                   failwith uu____13592
               | uu____13595 -> giveup env "head tag mismatch" orig)))
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
          (let uu____13627 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____13627
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____13635  ->
                  fun uu____13636  ->
                    match (uu____13635, uu____13636) with
                    | ((a1,uu____13646),(a2,uu____13648)) ->
                        let uu____13653 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_83  -> FStar_TypeChecker_Common.TProb _0_83)
                          uu____13653)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____13659 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p) FStar_Pervasives.fst)
                 sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____13659 in
           let wl1 = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____13679 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____13686)::[] -> wp1
              | uu____13699 ->
                  let uu____13705 =
                    let uu____13706 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____13706 in
                  failwith uu____13705 in
            let uu____13709 =
              let uu____13715 =
                let uu____13716 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____13716 in
              [uu____13715] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____13709;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____13717 = lift_c1 () in solve_eq uu____13717 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___133_13721  ->
                       match uu___133_13721 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____13722 -> false)) in
             let uu____13723 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____13747)::uu____13748,(wp2,uu____13750)::uu____13751)
                   -> (wp1, wp2)
               | uu____13792 ->
                   let uu____13805 =
                     let uu____13806 =
                       let uu____13809 =
                         let uu____13810 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____13811 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____13810 uu____13811 in
                       (uu____13809, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____13806 in
                   raise uu____13805 in
             match uu____13723 with
             | (wpc1,wpc2) ->
                 let uu____13828 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____13828
                 then
                   let uu____13831 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env uu____13831 wl
                 else
                   (let uu____13835 =
                      let uu____13839 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____13839 in
                    match uu____13835 with
                    | (c2_decl,qualifiers) ->
                        let uu____13851 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____13851
                        then
                          let c1_repr =
                            let uu____13854 =
                              let uu____13855 =
                                let uu____13856 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____13856 in
                              let uu____13857 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13855 uu____13857 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13854 in
                          let c2_repr =
                            let uu____13859 =
                              let uu____13860 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____13861 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13860 uu____13861 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13859 in
                          let prob =
                            let uu____13863 =
                              let uu____13866 =
                                let uu____13867 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____13868 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____13867
                                  uu____13868 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____13866 in
                            FStar_TypeChecker_Common.TProb uu____13863 in
                          let wl1 =
                            let uu____13870 =
                              let uu____13872 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives.fst in
                              Some uu____13872 in
                            solve_prob orig uu____13870 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____13879 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____13879
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____13881 =
                                     let uu____13884 =
                                       let uu____13885 =
                                         let uu____13895 =
                                           let uu____13896 =
                                             let uu____13897 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____13897] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____13896 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____13898 =
                                           let uu____13900 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____13901 =
                                             let uu____13903 =
                                               let uu____13904 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____13904 in
                                             [uu____13903] in
                                           uu____13900 :: uu____13901 in
                                         (uu____13895, uu____13898) in
                                       FStar_Syntax_Syntax.Tm_app uu____13885 in
                                     FStar_Syntax_Syntax.mk uu____13884 in
                                   uu____13881
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____13915 =
                                    let uu____13918 =
                                      let uu____13919 =
                                        let uu____13929 =
                                          let uu____13930 =
                                            let uu____13931 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____13931] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____13930 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____13932 =
                                          let uu____13934 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____13935 =
                                            let uu____13937 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____13938 =
                                              let uu____13940 =
                                                let uu____13941 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____13941 in
                                              [uu____13940] in
                                            uu____13937 :: uu____13938 in
                                          uu____13934 :: uu____13935 in
                                        (uu____13929, uu____13932) in
                                      FStar_Syntax_Syntax.Tm_app uu____13919 in
                                    FStar_Syntax_Syntax.mk uu____13918 in
                                  uu____13915
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____13952 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_TypeChecker_Common.TProb _0_84)
                               uu____13952 in
                           let wl1 =
                             let uu____13958 =
                               let uu____13960 =
                                 let uu____13963 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____13963 g in
                               FStar_All.pipe_left (fun _0_85  -> Some _0_85)
                                 uu____13960 in
                             solve_prob orig uu____13958 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____13973 = FStar_Util.physical_equality c1 c2 in
        if uu____13973
        then
          let uu____13974 = solve_prob orig None [] wl in
          solve env uu____13974
        else
          ((let uu____13977 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____13977
            then
              let uu____13978 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____13979 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____13978
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____13979
            else ());
           (let uu____13981 =
              let uu____13984 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____13985 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____13984, uu____13985) in
            match uu____13981 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____13989),FStar_Syntax_Syntax.Total
                    (t2,uu____13991)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14004 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14004 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14007,FStar_Syntax_Syntax.Total uu____14008) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14020),FStar_Syntax_Syntax.Total
                    (t2,uu____14022)) ->
                     let uu____14035 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14035 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14039),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14041)) ->
                     let uu____14054 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14054 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14058),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14060)) ->
                     let uu____14073 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14073 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14076,FStar_Syntax_Syntax.Comp uu____14077) ->
                     let uu____14083 =
                       let uu___177_14086 = problem in
                       let uu____14089 =
                         let uu____14090 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14090 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14086.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14089;
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14086.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___177_14086.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___177_14086.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14086.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14086.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14086.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14086.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14086.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14083 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14091,FStar_Syntax_Syntax.Comp uu____14092) ->
                     let uu____14098 =
                       let uu___177_14101 = problem in
                       let uu____14104 =
                         let uu____14105 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14105 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14101.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14104;
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14101.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___177_14101.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___177_14101.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14101.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14101.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14101.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14101.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14101.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14098 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14106,FStar_Syntax_Syntax.GTotal uu____14107) ->
                     let uu____14113 =
                       let uu___178_14116 = problem in
                       let uu____14119 =
                         let uu____14120 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14120 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14116.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___178_14116.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14116.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14119;
                         FStar_TypeChecker_Common.element =
                           (uu___178_14116.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14116.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14116.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14116.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14116.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14116.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14113 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14121,FStar_Syntax_Syntax.Total uu____14122) ->
                     let uu____14128 =
                       let uu___178_14131 = problem in
                       let uu____14134 =
                         let uu____14135 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14135 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14131.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___178_14131.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14131.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14134;
                         FStar_TypeChecker_Common.element =
                           (uu___178_14131.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14131.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14131.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14131.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14131.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14131.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14128 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14136,FStar_Syntax_Syntax.Comp uu____14137) ->
                     let uu____14138 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____14138
                     then
                       let uu____14139 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type" in
                       solve_t env uu____14139 wl
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
                           (let uu____14149 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____14149
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14151 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____14151 with
                            | None  ->
                                let uu____14153 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14154 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____14154) in
                                if uu____14153
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
                                  (let uu____14157 =
                                     let uu____14158 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____14159 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14158 uu____14159 in
                                   giveup env uu____14157 orig)
                            | Some edge -> solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14164 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14180  ->
              match uu____14180 with
              | (uu____14187,uu____14188,u,uu____14190,uu____14191,uu____14192)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____14164 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14210 =
        FStar_All.pipe_right (fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____14210 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____14220 =
        FStar_All.pipe_right (snd ineqs)
          (FStar_List.map
             (fun uu____14232  ->
                match uu____14232 with
                | (u1,u2) ->
                    let uu____14237 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____14238 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____14237 uu____14238)) in
      FStar_All.pipe_right uu____14220 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14250,[])) -> "{}"
      | uu____14263 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14273 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____14273
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____14276 =
              FStar_List.map
                (fun uu____14280  ->
                   match uu____14280 with
                   | (uu____14283,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____14276 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____14287 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14287 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14325 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____14325
    then
      let uu____14326 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____14327 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14326
        (rel_to_string rel) uu____14327
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
            let uu____14347 =
              let uu____14349 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_86  -> Some _0_86) uu____14349 in
            FStar_Syntax_Syntax.new_bv uu____14347 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____14355 =
              let uu____14357 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_87  -> Some _0_87) uu____14357 in
            let uu____14359 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____14355 uu____14359 in
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
          let uu____14382 = FStar_Options.eager_inference () in
          if uu____14382
          then
            let uu___179_14383 = probs in
            {
              attempting = (uu___179_14383.attempting);
              wl_deferred = (uu___179_14383.wl_deferred);
              ctr = (uu___179_14383.ctr);
              defer_ok = false;
              smt_ok = (uu___179_14383.smt_ok);
              tcenv = (uu___179_14383.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Syntax_Unionfind.rollback tx;
             (let uu____14394 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____14394
              then
                let uu____14395 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____14395
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
          ((let uu____14405 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____14405
            then
              let uu____14406 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14406
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____14410 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____14410
             then
               let uu____14411 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14411
             else ());
            (let f2 =
               let uu____14414 =
                 let uu____14415 = FStar_Syntax_Util.unmeta f1 in
                 uu____14415.FStar_Syntax_Syntax.n in
               match uu____14414 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14419 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___180_14420 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___180_14420.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___180_14420.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___180_14420.FStar_TypeChecker_Env.implicits)
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
            let uu____14435 =
              let uu____14436 =
                let uu____14437 =
                  let uu____14438 =
                    FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____14438
                    (fun _0_88  -> FStar_TypeChecker_Common.NonTrivial _0_88) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14437;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____14436 in
            FStar_All.pipe_left (fun _0_89  -> Some _0_89) uu____14435
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____14471 =
        let uu____14472 =
          let uu____14473 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
          FStar_All.pipe_right uu____14473
            (fun _0_90  -> FStar_TypeChecker_Common.NonTrivial _0_90) in
        {
          FStar_TypeChecker_Env.guard_f = uu____14472;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      Some uu____14471
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
          (let uu____14499 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14499
           then
             let uu____14500 = FStar_Syntax_Print.term_to_string t1 in
             let uu____14501 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14500
               uu____14501
           else ());
          (let prob =
             let uu____14504 =
               let uu____14507 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____14507 in
             FStar_All.pipe_left
               (fun _0_91  -> FStar_TypeChecker_Common.TProb _0_91)
               uu____14504 in
           let g =
             let uu____14512 =
               let uu____14514 = singleton' env prob smt_ok in
               solve_and_commit env uu____14514 (fun uu____14515  -> None) in
             FStar_All.pipe_left (with_guard env prob) uu____14512 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14529 = try_teq true env t1 t2 in
        match uu____14529 with
        | None  ->
            let uu____14531 =
              let uu____14532 =
                let uu____14535 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                let uu____14536 = FStar_TypeChecker_Env.get_range env in
                (uu____14535, uu____14536) in
              FStar_Errors.Error uu____14532 in
            raise uu____14531
        | Some g ->
            ((let uu____14539 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____14539
              then
                let uu____14540 = FStar_Syntax_Print.term_to_string t1 in
                let uu____14541 = FStar_Syntax_Print.term_to_string t2 in
                let uu____14542 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14540
                  uu____14541 uu____14542
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
          (let uu____14558 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14558
           then
             let uu____14559 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____14560 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14559
               uu____14560
           else ());
          (let uu____14562 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____14562 with
           | (prob,x) ->
               let g =
                 let uu____14570 =
                   let uu____14572 = singleton' env prob smt_ok in
                   solve_and_commit env uu____14572
                     (fun uu____14573  -> None) in
                 FStar_All.pipe_left (with_guard env prob) uu____14570 in
               ((let uu____14579 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____14579
                 then
                   let uu____14580 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____14581 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____14582 =
                     let uu____14583 = FStar_Util.must g in
                     guard_to_string env uu____14583 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14580 uu____14581 uu____14582
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
          let uu____14607 = FStar_TypeChecker_Env.get_range env in
          let uu____14608 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.err uu____14607 uu____14608
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____14620 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____14620
         then
           let uu____14621 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____14622 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____14621
             uu____14622
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____14627 =
             let uu____14630 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None uu____14630 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_92  -> FStar_TypeChecker_Common.CProb _0_92) uu____14627 in
         let uu____14633 =
           let uu____14635 = singleton env prob in
           solve_and_commit env uu____14635 (fun uu____14636  -> None) in
         FStar_All.pipe_left (with_guard env prob) uu____14633)
let solve_universe_inequalities':
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____14655  ->
        match uu____14655 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____14680 =
                 let uu____14681 =
                   let uu____14684 =
                     let uu____14685 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____14686 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____14685 uu____14686 in
                   let uu____14687 = FStar_TypeChecker_Env.get_range env in
                   (uu____14684, uu____14687) in
                 FStar_Errors.Error uu____14681 in
               raise uu____14680) in
            let equiv1 v1 v' =
              let uu____14695 =
                let uu____14698 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____14699 = FStar_Syntax_Subst.compress_univ v' in
                (uu____14698, uu____14699) in
              match uu____14695 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____14706 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____14720 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____14720 with
                      | FStar_Syntax_Syntax.U_unif uu____14724 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____14735  ->
                                    match uu____14735 with
                                    | (u,v') ->
                                        let uu____14741 = equiv1 v1 v' in
                                        if uu____14741
                                        then
                                          let uu____14743 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____14743 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____14753 -> [])) in
            let uu____14756 =
              let wl =
                let uu___181_14759 = empty_worklist env in
                {
                  attempting = (uu___181_14759.attempting);
                  wl_deferred = (uu___181_14759.wl_deferred);
                  ctr = (uu___181_14759.ctr);
                  defer_ok = false;
                  smt_ok = (uu___181_14759.smt_ok);
                  tcenv = (uu___181_14759.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____14766  ->
                      match uu____14766 with
                      | (lb,v1) ->
                          let uu____14771 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____14771 with
                           | USolved wl1 -> ()
                           | uu____14773 -> fail lb v1))) in
            let rec check_ineq uu____14779 =
              match uu____14779 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____14786) -> true
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
                      uu____14797,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____14799,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____14804) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____14808,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____14813 -> false) in
            let uu____14816 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____14822  ->
                      match uu____14822 with
                      | (u,v1) ->
                          let uu____14827 = check_ineq (u, v1) in
                          if uu____14827
                          then true
                          else
                            ((let uu____14830 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____14830
                              then
                                let uu____14831 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____14832 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____14831
                                  uu____14832
                              else ());
                             false))) in
            if uu____14816
            then ()
            else
              ((let uu____14836 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____14836
                then
                  ((let uu____14838 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____14838);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____14844 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____14844))
                else ());
               (let uu____14850 =
                  let uu____14851 =
                    let uu____14854 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____14854) in
                  FStar_Errors.Error uu____14851 in
                raise uu____14850))
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
      let fail uu____14887 =
        match uu____14887 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____14897 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____14897
       then
         let uu____14898 = wl_to_string wl in
         let uu____14899 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____14898 uu____14899
       else ());
      (let g1 =
         let uu____14911 = solve_and_commit env wl fail in
         match uu____14911 with
         | Some [] ->
             let uu___182_14918 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___182_14918.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___182_14918.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___182_14918.FStar_TypeChecker_Env.implicits)
             }
         | uu____14921 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___183_14924 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___183_14924.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___183_14924.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___183_14924.FStar_TypeChecker_Env.implicits)
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
            let uu___184_14950 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___184_14950.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___184_14950.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___184_14950.FStar_TypeChecker_Env.implicits)
            } in
          let uu____14951 =
            let uu____14952 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____14952 in
          if uu____14951
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____14958 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____14958
                   then
                     let uu____14959 = FStar_TypeChecker_Env.get_range env in
                     let uu____14960 =
                       let uu____14961 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____14961 in
                     FStar_Errors.diag uu____14959 uu____14960
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding] env vc in
                   let uu____14964 = check_trivial vc1 in
                   match uu____14964 with
                   | FStar_TypeChecker_Common.Trivial  -> Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then None
                       else
                         ((let uu____14971 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____14971
                           then
                             let uu____14972 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____14973 =
                               let uu____14974 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____14974 in
                             FStar_Errors.diag uu____14972 uu____14973
                           else ());
                          (let vcs =
                             let uu____14980 = FStar_Options.use_tactics () in
                             if uu____14980
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)] in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____14994  ->
                                   match uu____14994 with
                                   | (env1,goal) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify]
                                           env1 goal in
                                       let uu____15000 = check_trivial goal1 in
                                       (match uu____15000 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____15002 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____15002
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                                               ();
                                             (let uu____15007 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____15007
                                              then
                                                let uu____15008 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____15009 =
                                                  let uu____15010 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____15011 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____15010 uu____15011 in
                                                FStar_Errors.diag uu____15008
                                                  uu____15009
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
      let uu____15019 = discharge_guard' None env g false in
      match uu____15019 with
      | Some g1 -> g1
      | None  ->
          let uu____15024 =
            let uu____15025 =
              let uu____15028 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____15028) in
            FStar_Errors.Error uu____15025 in
          raise uu____15024
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15035 = discharge_guard' None env g true in
      match uu____15035 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____15047 = FStar_Syntax_Unionfind.find u in
      match uu____15047 with | None  -> true | uu____15049 -> false in
    let rec until_fixpoint acc implicits =
      let uu____15062 = acc in
      match uu____15062 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____15108 = hd1 in
               (match uu____15108 with
                | (uu____15115,env,u,tm,k,r) ->
                    let uu____15121 = unresolved u in
                    if uu____15121
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm in
                       (let uu____15139 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck") in
                        if uu____15139
                        then
                          let uu____15140 =
                            FStar_Syntax_Print.uvar_to_string u in
                          let uu____15141 =
                            FStar_Syntax_Print.term_to_string tm1 in
                          let uu____15142 =
                            FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____15140 uu____15141 uu____15142
                        else ());
                       (let uu____15144 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___185_15148 = env1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___185_15148.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___185_15148.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___185_15148.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___185_15148.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___185_15148.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___185_15148.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___185_15148.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___185_15148.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___185_15148.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___185_15148.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___185_15148.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___185_15148.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___185_15148.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___185_15148.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___185_15148.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___185_15148.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___185_15148.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___185_15148.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___185_15148.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___185_15148.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___185_15148.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___185_15148.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___185_15148.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___185_15148.FStar_TypeChecker_Env.proof_ns)
                             }) tm1 in
                        match uu____15144 with
                        | (uu____15149,uu____15150,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___186_15153 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___186_15153.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___186_15153.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___186_15153.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____15156 =
                                discharge_guard'
                                  (Some
                                     (fun uu____15160  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____15156 with
                              | Some g3 -> g3
                              | None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
    let uu___187_15175 = g in
    let uu____15176 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___187_15175.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___187_15175.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___187_15175.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____15176
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____15204 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____15204 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15211 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15211
      | (reason,uu____15213,uu____15214,e,t,r)::uu____15218 ->
          let uu____15232 =
            let uu____15233 = FStar_Syntax_Print.term_to_string t in
            let uu____15234 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format3
              "Failed to resolve implicit argument of type '%s' introduced in %s because %s"
              uu____15233 uu____15234 reason in
          FStar_Errors.err r uu____15232
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___188_15241 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___188_15241.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___188_15241.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___188_15241.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15259 = try_teq false env t1 t2 in
        match uu____15259 with
        | None  -> false
        | Some g ->
            let uu____15262 = discharge_guard' None env g false in
            (match uu____15262 with
             | Some uu____15266 -> true
             | None  -> false)