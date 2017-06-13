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
          (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_43  -> FStar_TypeChecker_Common.CProb _0_43)
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
          (fun _0_44  -> FStar_TypeChecker_Common.TProb _0_44) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_45  -> FStar_TypeChecker_Common.CProb _0_45) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____971 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____971 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____986  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1036 = next_pid () in
  let uu____1037 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1036;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1037;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1084 = next_pid () in
  let uu____1085 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1084;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1085;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1126 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1126;
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
        let uu____1178 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1178
        then
          let uu____1179 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1180 = prob_to_string env d in
          let uu____1181 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1179 uu____1180 uu____1181 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1186 -> failwith "impossible" in
           let uu____1187 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1195 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1196 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1195, uu____1196)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1200 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1201 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1200, uu____1201) in
           match uu____1187 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___119_1210  ->
            match uu___119_1210 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1216 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1218),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___120_1231  ->
           match uu___120_1231 with
           | UNIV uu____1233 -> None
           | TERM ((u,uu____1237),t) ->
               let uu____1241 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1241 then Some t else None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___121_1253  ->
           match uu___121_1253 with
           | UNIV (u',t) ->
               let uu____1257 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1257 then Some t else None
           | uu____1260 -> None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1267 =
        let uu____1268 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1268 in
      FStar_Syntax_Subst.compress uu____1267
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1275 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1275
let norm_arg env t = let uu____1294 = sn env (fst t) in (uu____1294, (snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1311  ->
              match uu____1311 with
              | (x,imp) ->
                  let uu____1318 =
                    let uu___144_1319 = x in
                    let uu____1320 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___144_1319.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___144_1319.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1320
                    } in
                  (uu____1318, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1335 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1335
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1338 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1338
        | uu____1340 -> u2 in
      let uu____1341 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1341
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1448 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____1448 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1460;
               FStar_Syntax_Syntax.pos = uu____1461;
               FStar_Syntax_Syntax.vars = uu____1462;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1483 =
                 let uu____1484 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1485 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1484
                   uu____1485 in
               failwith uu____1483)
    | FStar_Syntax_Syntax.Tm_uinst uu____1495 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1522 =
             let uu____1523 = FStar_Syntax_Subst.compress t1' in
             uu____1523.FStar_Syntax_Syntax.n in
           match uu____1522 with
           | FStar_Syntax_Syntax.Tm_refine uu____1535 -> aux true t1'
           | uu____1540 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1552 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1575 =
             let uu____1576 = FStar_Syntax_Subst.compress t1' in
             uu____1576.FStar_Syntax_Syntax.n in
           match uu____1575 with
           | FStar_Syntax_Syntax.Tm_refine uu____1588 -> aux true t1'
           | uu____1593 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_app uu____1605 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1637 =
             let uu____1638 = FStar_Syntax_Subst.compress t1' in
             uu____1638.FStar_Syntax_Syntax.n in
           match uu____1637 with
           | FStar_Syntax_Syntax.Tm_refine uu____1650 -> aux true t1'
           | uu____1655 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_type uu____1667 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_constant uu____1679 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_name uu____1691 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1703 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1715 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_abs uu____1734 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1760 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_let uu____1780 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_match uu____1799 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_meta uu____1826 ->
        let uu____1831 =
          let uu____1832 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1833 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1832
            uu____1833 in
        failwith uu____1831
    | FStar_Syntax_Syntax.Tm_ascribed uu____1843 ->
        let uu____1861 =
          let uu____1862 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1863 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1862
            uu____1863 in
        failwith uu____1861
    | FStar_Syntax_Syntax.Tm_delayed uu____1873 ->
        let uu____1894 =
          let uu____1895 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1896 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1895
            uu____1896 in
        failwith uu____1894
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1906 =
          let uu____1907 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1908 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1907
            uu____1908 in
        failwith uu____1906 in
  let uu____1918 = whnf env t1 in aux false uu____1918
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1927 =
        let uu____1937 = empty_worklist env in
        base_and_refinement env uu____1937 t in
      FStar_All.pipe_right uu____1927 FStar_Pervasives.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____1961 = FStar_Syntax_Syntax.null_bv t in
    (uu____1961, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____1981 = base_and_refinement env wl t in
  match uu____1981 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
let force_refinement uu____2040 =
  match uu____2040 with
  | (t_base,refopt) ->
      let uu____2054 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base in
      (match uu____2054 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___122_2078  ->
      match uu___122_2078 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2082 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2083 =
            let uu____2084 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____2084 in
          let uu____2085 =
            let uu____2086 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____2086 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2082 uu____2083
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2085
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2090 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2091 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____2092 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2090 uu____2091
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2092
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2096 =
      let uu____2098 =
        let uu____2100 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2110  ->
                  match uu____2110 with | (uu____2114,uu____2115,x) -> x)) in
        FStar_List.append wl.attempting uu____2100 in
      FStar_List.map (wl_prob_to_string wl) uu____2098 in
    FStar_All.pipe_right uu____2096 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2133 =
          let uu____2143 =
            let uu____2144 = FStar_Syntax_Subst.compress k in
            uu____2144.FStar_Syntax_Syntax.n in
          match uu____2143 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2189 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2189)
              else
                (let uu____2203 = FStar_Syntax_Util.abs_formals t in
                 match uu____2203 with
                 | (ys',t1,uu____2224) ->
                     let uu____2237 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2237))
          | uu____2258 ->
              let uu____2259 =
                let uu____2265 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____2265) in
              ((ys, t), uu____2259) in
        match uu____2133 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2324 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2324 c in
               let uu____2326 =
                 let uu____2333 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_46  -> FStar_Util.Inl _0_46) in
                 FStar_All.pipe_right uu____2333 (fun _0_47  -> Some _0_47) in
               FStar_Syntax_Util.abs ys1 t1 uu____2326)
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
            let uu____2384 = p_guard prob in
            match uu____2384 with
            | (uu____2387,uv) ->
                ((let uu____2390 =
                    let uu____2391 = FStar_Syntax_Subst.compress uv in
                    uu____2391.FStar_Syntax_Syntax.n in
                  match uu____2390 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2411 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2411
                        then
                          let uu____2412 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2413 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2414 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2412
                            uu____2413 uu____2414
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2416 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___145_2419 = wl in
                  {
                    attempting = (uu___145_2419.attempting);
                    wl_deferred = (uu___145_2419.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___145_2419.defer_ok);
                    smt_ok = (uu___145_2419.smt_ok);
                    tcenv = (uu___145_2419.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2432 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2432
         then
           let uu____2433 = FStar_Util.string_of_int pid in
           let uu____2434 =
             let uu____2435 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2435 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2433 uu____2434
         else ());
        commit sol;
        (let uu___146_2440 = wl in
         {
           attempting = (uu___146_2440.attempting);
           wl_deferred = (uu___146_2440.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___146_2440.defer_ok);
           smt_ok = (uu___146_2440.smt_ok);
           tcenv = (uu___146_2440.tcenv)
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
            | (uu____2469,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2477 = FStar_Syntax_Util.mk_conj t1 f in
                Some uu____2477 in
          (let uu____2483 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2483
           then
             let uu____2484 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2485 =
               let uu____2486 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2486 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2484 uu____2485
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2511 =
    let uu____2515 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2515 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2511
    (FStar_Util.for_some
       (fun uu____2532  ->
          match uu____2532 with
          | (uv,uu____2536) -> FStar_Syntax_Unionfind.equiv uv (fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2569 = occurs wl uk t in Prims.op_Negation uu____2569 in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2574 =
         let uu____2575 = FStar_Syntax_Print.uvar_to_string (fst uk) in
         let uu____2576 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2575 uu____2576 in
       Some uu____2574) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2624 = occurs_check env wl uk t in
  match uu____2624 with
  | (occurs_ok,msg) ->
      let uu____2641 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2641, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2705 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2729  ->
            fun uu____2730  ->
              match (uu____2729, uu____2730) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2773 =
                    let uu____2774 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2774 in
                  if uu____2773
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2788 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2788
                     then
                       let uu____2795 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____2795)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2705 with | (isect,uu____2817) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2870  ->
          fun uu____2871  ->
            match (uu____2870, uu____2871) with
            | ((a,uu____2881),(b,uu____2883)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2927 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2933  ->
                match uu____2933 with
                | (b,uu____2937) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____2927 then None else Some (a, (snd hd1))
  | uu____2946 -> None
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
            let uu____2989 = pat_var_opt env seen hd1 in
            (match uu____2989 with
             | None  ->
                 ((let uu____2997 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____2997
                   then
                     let uu____2998 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____2998
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3010 =
      let uu____3011 = FStar_Syntax_Subst.compress t in
      uu____3011.FStar_Syntax_Syntax.n in
    match uu____3010 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3014 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3023;
           FStar_Syntax_Syntax.tk = uu____3024;
           FStar_Syntax_Syntax.pos = uu____3025;
           FStar_Syntax_Syntax.vars = uu____3026;_},uu____3027)
        -> true
    | uu____3050 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3112;
         FStar_Syntax_Syntax.pos = uu____3113;
         FStar_Syntax_Syntax.vars = uu____3114;_},args)
      -> (t, uv, k, args)
  | uu____3155 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____3209 = destruct_flex_t t in
  match uu____3209 with
  | (t1,uv,k,args) ->
      let uu____3277 = pat_vars env [] args in
      (match uu____3277 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3333 -> ((t1, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth option*
  FStar_Syntax_Syntax.delta_depth option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3382 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth option* FStar_Syntax_Syntax.delta_depth
      option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3405 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3409 -> false
let head_match: match_result -> match_result =
  fun uu___123_3412  ->
    match uu___123_3412 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3421 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3434 ->
          let uu____3435 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3435 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3445 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3459 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3465 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> None
      | FStar_Syntax_Syntax.Tm_bvar uu____3487 -> None
      | FStar_Syntax_Syntax.Tm_name uu____3488 -> None
      | FStar_Syntax_Syntax.Tm_uvar uu____3489 -> None
      | FStar_Syntax_Syntax.Tm_let uu____3498 -> None
      | FStar_Syntax_Syntax.Tm_match uu____3506 -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3523) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3529,uu____3530) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3560) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3575;
             FStar_Syntax_Syntax.index = uu____3576;
             FStar_Syntax_Syntax.sort = t2;_},uu____3578)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3585 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3586 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3587 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3595 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3611 = fv_delta_depth env fv in Some uu____3611
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
            let uu____3630 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3630
            then FullMatch
            else
              (let uu____3632 =
                 let uu____3637 =
                   let uu____3639 = fv_delta_depth env f in Some uu____3639 in
                 let uu____3640 =
                   let uu____3642 = fv_delta_depth env g in Some uu____3642 in
                 (uu____3637, uu____3640) in
               MisMatch uu____3632)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3646),FStar_Syntax_Syntax.Tm_uinst (g,uu____3648)) ->
            let uu____3657 = head_matches env f g in
            FStar_All.pipe_right uu____3657 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3664),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3666)) ->
            let uu____3691 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____3691 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3696),FStar_Syntax_Syntax.Tm_refine (y,uu____3698)) ->
            let uu____3707 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3707 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3709),uu____3710) ->
            let uu____3715 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3715 head_match
        | (uu____3716,FStar_Syntax_Syntax.Tm_refine (x,uu____3718)) ->
            let uu____3723 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3723 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3724,FStar_Syntax_Syntax.Tm_type
           uu____3725) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3726,FStar_Syntax_Syntax.Tm_arrow uu____3727) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3743),FStar_Syntax_Syntax.Tm_app (head',uu____3745))
            ->
            let uu____3774 = head_matches env head1 head' in
            FStar_All.pipe_right uu____3774 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3776),uu____3777) ->
            let uu____3792 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____3792 head_match
        | (uu____3793,FStar_Syntax_Syntax.Tm_app (head1,uu____3795)) ->
            let uu____3810 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____3810 head_match
        | uu____3811 ->
            let uu____3814 =
              let uu____3819 = delta_depth_of_term env t11 in
              let uu____3821 = delta_depth_of_term env t21 in
              (uu____3819, uu____3821) in
            MisMatch uu____3814
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3857 = FStar_Syntax_Util.head_and_args t in
    match uu____3857 with
    | (head1,uu____3869) ->
        let uu____3884 =
          let uu____3885 = FStar_Syntax_Util.un_uinst head1 in
          uu____3885.FStar_Syntax_Syntax.n in
        (match uu____3884 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3890 =
               let uu____3891 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____3891 FStar_Option.isSome in
             if uu____3890
             then
               let uu____3905 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____3905 (fun _0_48  -> Some _0_48)
             else None
         | uu____3908 -> None) in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None)) in
  let fail r = (r, None) in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21 in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),uu____3976) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____3986 =
             let uu____3991 = maybe_inline t11 in
             let uu____3993 = maybe_inline t21 in (uu____3991, uu____3993) in
           match uu____3986 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (uu____4014,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4024 =
             let uu____4029 = maybe_inline t11 in
             let uu____4031 = maybe_inline t21 in (uu____4029, uu____4031) in
           match uu____4024 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____4056 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____4056 with
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
        let uu____4071 =
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
             let uu____4079 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____4079)) in
        (match uu____4071 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4087 -> fail r
    | uu____4092 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4121 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4151 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4166 = FStar_Syntax_Util.type_u () in
      match uu____4166 with
      | (t,uu____4170) ->
          let uu____4171 = new_uvar r binders t in fst uu____4171
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4180 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____4180 FStar_Pervasives.fst
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
        let uu____4222 = head_matches env t1 t' in
        match uu____4222 with
        | MisMatch uu____4223 -> false
        | uu____4228 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4288,imp),T (t2,uu____4291)) -> (t2, imp)
                     | uu____4308 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4348  ->
                    match uu____4348 with
                    | (t2,uu____4356) ->
                        (None, INVARIANT, (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let fail uu____4389 = failwith "Bad reconstruction" in
          let uu____4390 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____4390 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4443))::tcs2) ->
                       aux
                         (((let uu___147_4465 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___147_4465.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___147_4465.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4475 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___124_4506 =
                 match uu___124_4506 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4569 = decompose1 [] bs1 in
               (rebuild, matches, uu____4569))
      | uu____4597 ->
          let rebuild uu___125_4602 =
            match uu___125_4602 with
            | [] -> t1
            | uu____4604 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___126_4623  ->
    match uu___126_4623 with
    | T (t,uu____4625) -> t
    | uu____4634 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___127_4637  ->
    match uu___127_4637 with
    | T (t,uu____4639) -> FStar_Syntax_Syntax.as_arg t
    | uu____4648 -> failwith "Impossible"
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
              | (uu____4717,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4736 = new_uvar r scope1 k in
                  (match uu____4736 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4748 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args)) None r in
                       let uu____4763 =
                         let uu____4764 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_49  ->
                              FStar_TypeChecker_Common.TProb _0_49)
                           uu____4764 in
                       ((T (gi_xs, mk_kind)), uu____4763))
              | (uu____4773,uu____4774,C uu____4775) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4862 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4873;
                         FStar_Syntax_Syntax.pos = uu____4874;
                         FStar_Syntax_Syntax.vars = uu____4875;_})
                        ->
                        let uu____4890 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4890 with
                         | (T (gi_xs,uu____4906),prob) ->
                             let uu____4916 =
                               let uu____4917 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_50  -> C _0_50)
                                 uu____4917 in
                             (uu____4916, [prob])
                         | uu____4919 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4929;
                         FStar_Syntax_Syntax.pos = uu____4930;
                         FStar_Syntax_Syntax.vars = uu____4931;_})
                        ->
                        let uu____4946 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4946 with
                         | (T (gi_xs,uu____4962),prob) ->
                             let uu____4972 =
                               let uu____4973 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_51  -> C _0_51)
                                 uu____4973 in
                             (uu____4972, [prob])
                         | uu____4975 -> failwith "impossible")
                    | (uu____4981,uu____4982,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____4984;
                         FStar_Syntax_Syntax.pos = uu____4985;
                         FStar_Syntax_Syntax.vars = uu____4986;_})
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
                        let uu____5060 =
                          let uu____5065 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____5065 FStar_List.unzip in
                        (match uu____5060 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5094 =
                                 let uu____5095 =
                                   let uu____5098 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____5098 un_T in
                                 let uu____5099 =
                                   let uu____5105 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____5105
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5095;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5099;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5094 in
                             ((C gi_xs), sub_probs))
                    | uu____5110 ->
                        let uu____5117 = sub_prob scope1 args q in
                        (match uu____5117 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____4862 with
                   | (tc,probs) ->
                       let uu____5135 =
                         match q with
                         | (Some b,uu____5161,uu____5162) ->
                             let uu____5170 =
                               let uu____5174 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____5174 :: args in
                             ((Some b), (b :: scope1), uu____5170)
                         | uu____5192 -> (None, scope1, args) in
                       (match uu____5135 with
                        | (bopt,scope2,args1) ->
                            let uu____5235 = aux scope2 args1 qs2 in
                            (match uu____5235 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____5256 =
                                         let uu____5258 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         f :: uu____5258 in
                                       FStar_Syntax_Util.mk_conj_l uu____5256
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (fst b).FStar_Syntax_Syntax.sort in
                                       let uu____5271 =
                                         let uu____5273 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (fst b) f in
                                         let uu____5274 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         uu____5273 :: uu____5274 in
                                       FStar_Syntax_Util.mk_conj_l uu____5271 in
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
  let uu___148_5327 = p in
  let uu____5330 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____5331 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___148_5327.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5330;
    FStar_TypeChecker_Common.relation =
      (uu___148_5327.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5331;
    FStar_TypeChecker_Common.element =
      (uu___148_5327.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___148_5327.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___148_5327.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___148_5327.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___148_5327.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___148_5327.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5341 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____5341
            (fun _0_52  -> FStar_TypeChecker_Common.TProb _0_52)
      | FStar_TypeChecker_Common.CProb uu____5346 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5360 = compress_prob wl pr in
        FStar_All.pipe_right uu____5360 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5366 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____5366 with
           | (lh,uu____5379) ->
               let uu____5394 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____5394 with
                | (rh,uu____5407) ->
                    let uu____5422 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5431,FStar_Syntax_Syntax.Tm_uvar uu____5432)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5451,uu____5452)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5463,FStar_Syntax_Syntax.Tm_uvar uu____5464)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5475,uu____5476)
                          ->
                          let uu____5485 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5485 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5525 ->
                                    let rank =
                                      let uu____5532 = is_top_level_prob prob in
                                      if uu____5532
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5534 =
                                      let uu___149_5537 = tp in
                                      let uu____5540 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_5537.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___149_5537.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_5537.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5540;
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_5537.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_5537.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_5537.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_5537.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_5537.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_5537.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5534)))
                      | (uu____5550,FStar_Syntax_Syntax.Tm_uvar uu____5551)
                          ->
                          let uu____5560 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5560 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5600 ->
                                    let uu____5606 =
                                      let uu___150_5611 = tp in
                                      let uu____5614 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___150_5611.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5614;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___150_5611.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___150_5611.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___150_5611.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___150_5611.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___150_5611.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___150_5611.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___150_5611.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___150_5611.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5606)))
                      | (uu____5630,uu____5631) -> (rigid_rigid, tp) in
                    (match uu____5422 with
                     | (rank,tp1) ->
                         let uu____5642 =
                           FStar_All.pipe_right
                             (let uu___151_5645 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___151_5645.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___151_5645.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___151_5645.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___151_5645.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___151_5645.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___151_5645.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___151_5645.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___151_5645.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___151_5645.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_53  ->
                                FStar_TypeChecker_Common.TProb _0_53) in
                         (rank, uu____5642))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5651 =
            FStar_All.pipe_right
              (let uu___152_5654 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___152_5654.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___152_5654.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___152_5654.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___152_5654.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___152_5654.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___152_5654.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___152_5654.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___152_5654.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___152_5654.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_54  -> FStar_TypeChecker_Common.CProb _0_54) in
          (rigid_rigid, uu____5651)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob option* FStar_TypeChecker_Common.prob
      Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____5686 probs =
      match uu____5686 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5716 = rank wl hd1 in
               (match uu____5716 with
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
    match projectee with | UDeferred _0 -> true | uu____5784 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5796 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5808 -> false
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
                        let uu____5841 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____5841 with
                        | (k,uu____5845) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____5849 -> false)))
            | uu____5850 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____5897 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____5897 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5900 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____5906 =
                     let uu____5907 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____5908 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5907
                       uu____5908 in
                   UFailed uu____5906)
            | (FStar_Syntax_Syntax.U_max us,u') ->
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
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5942 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5942 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____5945 ->
                let uu____5948 =
                  let uu____5949 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____5950 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5949
                    uu____5950 msg in
                UFailed uu____5948 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____5951,uu____5952) ->
              let uu____5953 =
                let uu____5954 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5955 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5954 uu____5955 in
              failwith uu____5953
          | (FStar_Syntax_Syntax.U_unknown ,uu____5956) ->
              let uu____5957 =
                let uu____5958 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5959 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5958 uu____5959 in
              failwith uu____5957
          | (uu____5960,FStar_Syntax_Syntax.U_bvar uu____5961) ->
              let uu____5962 =
                let uu____5963 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5964 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5963 uu____5964 in
              failwith uu____5962
          | (uu____5965,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____5966 =
                let uu____5967 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5968 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5967 uu____5968 in
              failwith uu____5966
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____5980 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____5980
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____5990 = occurs_univ v1 u3 in
              if uu____5990
              then
                let uu____5991 =
                  let uu____5992 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____5993 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5992 uu____5993 in
                try_umax_components u11 u21 uu____5991
              else
                (let uu____5995 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____5995)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____6003 = occurs_univ v1 u3 in
              if uu____6003
              then
                let uu____6004 =
                  let uu____6005 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6006 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6005 uu____6006 in
                try_umax_components u11 u21 uu____6004
              else
                (let uu____6008 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6008)
          | (FStar_Syntax_Syntax.U_max uu____6011,uu____6012) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6017 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6017
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____6019,FStar_Syntax_Syntax.U_max uu____6020) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6025 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6025
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6027,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6028,FStar_Syntax_Syntax.U_name
             uu____6029) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6030) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6031) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6032,FStar_Syntax_Syntax.U_succ
             uu____6033) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6034,FStar_Syntax_Syntax.U_zero
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
  let uu____6096 = bc1 in
  match uu____6096 with
  | (bs1,mk_cod1) ->
      let uu____6121 = bc2 in
      (match uu____6121 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6168 = FStar_Util.first_N n1 bs in
             match uu____6168 with
             | (bs3,rest) ->
                 let uu____6182 = mk_cod rest in (bs3, uu____6182) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____6206 =
               let uu____6210 = mk_cod1 [] in (bs1, uu____6210) in
             let uu____6212 =
               let uu____6216 = mk_cod2 [] in (bs2, uu____6216) in
             (uu____6206, uu____6212)
           else
             if l1 > l2
             then
               (let uu____6243 = curry l2 bs1 mk_cod1 in
                let uu____6253 =
                  let uu____6257 = mk_cod2 [] in (bs2, uu____6257) in
                (uu____6243, uu____6253))
             else
               (let uu____6266 =
                  let uu____6270 = mk_cod1 [] in (bs1, uu____6270) in
                let uu____6272 = curry l1 bs2 mk_cod2 in
                (uu____6266, uu____6272)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6379 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____6379
       then
         let uu____6380 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6380
       else ());
      (let uu____6382 = next_prob probs in
       match uu____6382 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___153_6395 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___153_6395.wl_deferred);
               ctr = (uu___153_6395.ctr);
               defer_ok = (uu___153_6395.defer_ok);
               smt_ok = (uu___153_6395.smt_ok);
               tcenv = (uu___153_6395.tcenv)
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
                  let uu____6402 = solve_flex_rigid_join env tp probs1 in
                  (match uu____6402 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6406 = solve_rigid_flex_meet env tp probs1 in
                     match uu____6406 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____6410,uu____6411) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6420 ->
                let uu____6425 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6453  ->
                          match uu____6453 with
                          | (c,uu____6458,uu____6459) -> c < probs.ctr)) in
                (match uu____6425 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6481 =
                            FStar_List.map
                              (fun uu____6487  ->
                                 match uu____6487 with
                                 | (uu____6493,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____6481
                      | uu____6496 ->
                          let uu____6501 =
                            let uu___154_6502 = probs in
                            let uu____6503 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6512  ->
                                      match uu____6512 with
                                      | (uu____6516,uu____6517,y) -> y)) in
                            {
                              attempting = uu____6503;
                              wl_deferred = rest;
                              ctr = (uu___154_6502.ctr);
                              defer_ok = (uu___154_6502.defer_ok);
                              smt_ok = (uu___154_6502.smt_ok);
                              tcenv = (uu___154_6502.tcenv)
                            } in
                          solve env uu____6501))))
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
            let uu____6524 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____6524 with
            | USolved wl1 ->
                let uu____6526 = solve_prob orig None [] wl1 in
                solve env uu____6526
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
                  let uu____6560 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6560 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6563 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6571;
                  FStar_Syntax_Syntax.pos = uu____6572;
                  FStar_Syntax_Syntax.vars = uu____6573;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6576;
                  FStar_Syntax_Syntax.pos = uu____6577;
                  FStar_Syntax_Syntax.vars = uu____6578;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6590,uu____6591) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6596,FStar_Syntax_Syntax.Tm_uinst uu____6597) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6602 -> USolved wl
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
            ((let uu____6610 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6610
              then
                let uu____6611 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6611 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6619 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6619
         then
           let uu____6620 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6620
         else ());
        (let uu____6622 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6622 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6664 = head_matches_delta env () t1 t2 in
               match uu____6664 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6686 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6712 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6721 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____6722 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____6721, uu____6722)
                          | None  ->
                              let uu____6725 = FStar_Syntax_Subst.compress t1 in
                              let uu____6726 = FStar_Syntax_Subst.compress t2 in
                              (uu____6725, uu____6726) in
                        (match uu____6712 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6748 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_55  ->
                                    FStar_TypeChecker_Common.TProb _0_55)
                                 uu____6748 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6771 =
                                    let uu____6777 =
                                      let uu____6780 =
                                        let uu____6783 =
                                          let uu____6784 =
                                            let uu____6789 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____6789) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6784 in
                                        FStar_Syntax_Syntax.mk uu____6783 in
                                      uu____6780 None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____6802 =
                                      let uu____6804 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____6804] in
                                    (uu____6777, uu____6802) in
                                  Some uu____6771
                              | (uu____6813,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6815)) ->
                                  let uu____6820 =
                                    let uu____6824 =
                                      let uu____6826 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____6826] in
                                    (t11, uu____6824) in
                                  Some uu____6820
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6832),uu____6833) ->
                                  let uu____6838 =
                                    let uu____6842 =
                                      let uu____6844 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____6844] in
                                    (t21, uu____6842) in
                                  Some uu____6838
                              | uu____6849 ->
                                  let uu____6852 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____6852 with
                                   | (head1,uu____6867) ->
                                       let uu____6882 =
                                         let uu____6883 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____6883.FStar_Syntax_Syntax.n in
                                       (match uu____6882 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6890;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6892;_}
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
                                        | uu____6901 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6910) ->
                  let uu____6923 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___128_6932  ->
                            match uu___128_6932 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6937 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____6937 with
                                      | (u',uu____6948) ->
                                          let uu____6963 =
                                            let uu____6964 = whnf env u' in
                                            uu____6964.FStar_Syntax_Syntax.n in
                                          (match uu____6963 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____6968) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____6981 -> false))
                                 | uu____6982 -> false)
                            | uu____6984 -> false)) in
                  (match uu____6923 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____7005 tps =
                         match uu____7005 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7032 =
                                    let uu____7037 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____7037 in
                                  (match uu____7032 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____7056 -> None) in
                       let uu____7061 =
                         let uu____7066 =
                           let uu____7070 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____7070, []) in
                         make_lower_bound uu____7066 lower_bounds in
                       (match uu____7061 with
                        | None  ->
                            ((let uu____7077 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7077
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
                            ((let uu____7090 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7090
                              then
                                let wl' =
                                  let uu___155_7092 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___155_7092.wl_deferred);
                                    ctr = (uu___155_7092.ctr);
                                    defer_ok = (uu___155_7092.defer_ok);
                                    smt_ok = (uu___155_7092.smt_ok);
                                    tcenv = (uu___155_7092.tcenv)
                                  } in
                                let uu____7093 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7093
                              else ());
                             (let uu____7095 =
                                solve_t env eq_prob
                                  (let uu___156_7096 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___156_7096.wl_deferred);
                                     ctr = (uu___156_7096.ctr);
                                     defer_ok = (uu___156_7096.defer_ok);
                                     smt_ok = (uu___156_7096.smt_ok);
                                     tcenv = (uu___156_7096.tcenv)
                                   }) in
                              match uu____7095 with
                              | Success uu____7098 ->
                                  let wl1 =
                                    let uu___157_7100 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___157_7100.wl_deferred);
                                      ctr = (uu___157_7100.ctr);
                                      defer_ok = (uu___157_7100.defer_ok);
                                      smt_ok = (uu___157_7100.smt_ok);
                                      tcenv = (uu___157_7100.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1 in
                                  let uu____7102 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds in
                                  Some wl2
                              | uu____7105 -> None))))
              | uu____7106 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7113 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____7113
         then
           let uu____7114 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7114
         else ());
        (let uu____7116 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____7116 with
         | (u,args) ->
             let uu____7143 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____7143 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____7174 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____7174 with
                    | (h1,args1) ->
                        let uu____7202 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____7202 with
                         | (h2,uu____7215) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7234 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____7234
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7249 =
                                          let uu____7251 =
                                            let uu____7252 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_56  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_56) uu____7252 in
                                          [uu____7251] in
                                        Some uu____7249))
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
                                       (let uu____7276 =
                                          let uu____7278 =
                                            let uu____7279 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_57  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_57) uu____7279 in
                                          [uu____7278] in
                                        Some uu____7276))
                                  else None
                              | uu____7287 -> None)) in
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
                             let uu____7353 =
                               let uu____7359 =
                                 let uu____7362 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____7362 in
                               (uu____7359, m1) in
                             Some uu____7353)
                    | (uu____7371,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7373)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7405),uu____7406) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____7437 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7471) ->
                       let uu____7484 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___129_7493  ->
                                 match uu___129_7493 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____7498 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____7498 with
                                           | (u',uu____7509) ->
                                               let uu____7524 =
                                                 let uu____7525 = whnf env u' in
                                                 uu____7525.FStar_Syntax_Syntax.n in
                                               (match uu____7524 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7529) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____7542 -> false))
                                      | uu____7543 -> false)
                                 | uu____7545 -> false)) in
                       (match uu____7484 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7570 tps =
                              match uu____7570 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7611 =
                                         let uu____7618 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7618 in
                                       (match uu____7611 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7653 -> None) in
                            let uu____7660 =
                              let uu____7667 =
                                let uu____7673 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7673, []) in
                              make_upper_bound uu____7667 upper_bounds in
                            (match uu____7660 with
                             | None  ->
                                 ((let uu____7682 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7682
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
                                 ((let uu____7701 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7701
                                   then
                                     let wl' =
                                       let uu___158_7703 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___158_7703.wl_deferred);
                                         ctr = (uu___158_7703.ctr);
                                         defer_ok = (uu___158_7703.defer_ok);
                                         smt_ok = (uu___158_7703.smt_ok);
                                         tcenv = (uu___158_7703.tcenv)
                                       } in
                                     let uu____7704 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7704
                                   else ());
                                  (let uu____7706 =
                                     solve_t env eq_prob
                                       (let uu___159_7707 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___159_7707.wl_deferred);
                                          ctr = (uu___159_7707.ctr);
                                          defer_ok = (uu___159_7707.defer_ok);
                                          smt_ok = (uu___159_7707.smt_ok);
                                          tcenv = (uu___159_7707.tcenv)
                                        }) in
                                   match uu____7706 with
                                   | Success uu____7709 ->
                                       let wl1 =
                                         let uu___160_7711 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___160_7711.wl_deferred);
                                           ctr = (uu___160_7711.ctr);
                                           defer_ok =
                                             (uu___160_7711.defer_ok);
                                           smt_ok = (uu___160_7711.smt_ok);
                                           tcenv = (uu___160_7711.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1 in
                                       let uu____7713 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds in
                                       Some wl2
                                   | uu____7716 -> None))))
                   | uu____7717 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____7782 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____7782
                      then
                        let uu____7783 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7783
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___161_7815 = hd1 in
                      let uu____7816 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_7815.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_7815.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7816
                      } in
                    let hd21 =
                      let uu___162_7820 = hd2 in
                      let uu____7821 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___162_7820.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___162_7820.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7821
                      } in
                    let prob =
                      let uu____7825 =
                        let uu____7828 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7828 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_58  -> FStar_TypeChecker_Common.TProb _0_58)
                        uu____7825 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____7836 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7836 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____7839 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____7839 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7857 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives.fst in
                           let uu____7860 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____7857 uu____7860 in
                         ((let uu____7866 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____7866
                           then
                             let uu____7867 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____7868 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7867 uu____7868
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7883 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____7889 = aux scope env [] bs1 bs2 in
              match uu____7889 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7905 = compress_tprob wl problem in
        solve_t' env uu____7905 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7938 = head_matches_delta env1 wl1 t1 t2 in
          match uu____7938 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7955,uu____7956) ->
                   let may_relate head3 =
                     let uu____7971 =
                       let uu____7972 = FStar_Syntax_Util.un_uinst head3 in
                       uu____7972.FStar_Syntax_Syntax.n in
                     match uu____7971 with
                     | FStar_Syntax_Syntax.Tm_name uu____7975 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____7976 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____7993 -> false in
                   let uu____7994 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____7994
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
                                let uu____8011 =
                                  let uu____8012 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____8012 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____8011 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____8014 = solve_prob orig (Some guard) [] wl1 in
                     solve env1 uu____8014
                   else
                     (let uu____8016 =
                        let uu____8017 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____8018 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____8017 uu____8018 in
                      giveup env1 uu____8016 orig)
               | (uu____8019,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___163_8027 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___163_8027.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___163_8027.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___163_8027.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___163_8027.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___163_8027.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___163_8027.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___163_8027.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___163_8027.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____8028,None ) ->
                   ((let uu____8035 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8035
                     then
                       let uu____8036 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____8037 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____8038 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____8039 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____8036
                         uu____8037 uu____8038 uu____8039
                     else ());
                    (let uu____8041 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____8041 with
                     | (head11,args1) ->
                         let uu____8067 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____8067 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8112 =
                                  let uu____8113 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____8114 = args_to_string args1 in
                                  let uu____8115 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____8116 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8113 uu____8114 uu____8115
                                    uu____8116 in
                                giveup env1 uu____8112 orig
                              else
                                (let uu____8118 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8123 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____8123 = FStar_Syntax_Util.Equal) in
                                 if uu____8118
                                 then
                                   let uu____8124 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____8124 with
                                   | USolved wl2 ->
                                       let uu____8126 =
                                         solve_prob orig None [] wl2 in
                                       solve env1 uu____8126
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8130 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____8130 with
                                    | (base1,refinement1) ->
                                        let uu____8156 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____8156 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____8210 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____8210 with
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
                                                           (fun uu____8220 
                                                              ->
                                                              fun uu____8221 
                                                                ->
                                                                match 
                                                                  (uu____8220,
                                                                    uu____8221)
                                                                with
                                                                | ((a,uu____8231),
                                                                   (a',uu____8233))
                                                                    ->
                                                                    let uu____8238
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
                                                                    uu____8238)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____8244 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8244 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8248 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___164_8281 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___164_8281.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___164_8281.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___164_8281.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___164_8281.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___164_8281.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___164_8281.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___164_8281.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___164_8281.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____8301 = p in
          match uu____8301 with
          | (((u,k),xs,c),ps,(h,uu____8312,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8361 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____8361 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8375 = h gs_xs in
                     let uu____8376 =
                       let uu____8383 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_60  -> FStar_Util.Inl _0_60) in
                       FStar_All.pipe_right uu____8383
                         (fun _0_61  -> Some _0_61) in
                     FStar_Syntax_Util.abs xs1 uu____8375 uu____8376 in
                   ((let uu____8414 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8414
                     then
                       let uu____8415 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____8416 = FStar_Syntax_Print.comp_to_string c in
                       let uu____8417 = FStar_Syntax_Print.term_to_string im in
                       let uu____8418 = FStar_Syntax_Print.tag_of_term im in
                       let uu____8419 =
                         let uu____8420 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____8420
                           (FStar_String.concat ", ") in
                       let uu____8423 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8415 uu____8416 uu____8417 uu____8418
                         uu____8419 uu____8423
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___130_8441 =
          match uu___130_8441 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____8470 = p in
          match uu____8470 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8528 = FStar_List.nth ps i in
              (match uu____8528 with
               | (pi,uu____8531) ->
                   let uu____8536 = FStar_List.nth xs i in
                   (match uu____8536 with
                    | (xi,uu____8543) ->
                        let rec gs k =
                          let uu____8552 = FStar_Syntax_Util.arrow_formals k in
                          match uu____8552 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8604)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8612 = new_uvar r xs k_a in
                                    (match uu____8612 with
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
                                         let uu____8631 = aux subst2 tl1 in
                                         (match uu____8631 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8646 =
                                                let uu____8648 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8648 :: gi_xs' in
                                              let uu____8649 =
                                                let uu____8651 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8651 :: gi_ps' in
                                              (uu____8646, uu____8649))) in
                              aux [] bs in
                        let uu____8654 =
                          let uu____8655 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8655 in
                        if uu____8654
                        then None
                        else
                          (let uu____8658 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8658 with
                           | (g_xs,uu____8665) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8672 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r in
                                 let uu____8677 =
                                   let uu____8684 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_62  -> FStar_Util.Inl _0_62) in
                                   FStar_All.pipe_right uu____8684
                                     (fun _0_63  -> Some _0_63) in
                                 FStar_Syntax_Util.abs xs uu____8672
                                   uu____8677 in
                               let sub1 =
                                 let uu____8715 =
                                   let uu____8718 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let uu____8725 =
                                     let uu____8728 =
                                       FStar_List.map
                                         (fun uu____8734  ->
                                            match uu____8734 with
                                            | (uu____8739,uu____8740,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____8728 in
                                   mk_problem (p_scope orig) orig uu____8718
                                     (p_rel orig) uu____8725 None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____8715 in
                               ((let uu____8750 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____8750
                                 then
                                   let uu____8751 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____8752 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8751 uu____8752
                                 else ());
                                (let wl2 =
                                   let uu____8755 =
                                     let uu____8757 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives.fst (p_guard sub1) in
                                     Some uu____8757 in
                                   solve_prob orig uu____8755
                                     [TERM (u, proj)] wl1 in
                                 let uu____8762 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_65  -> Some _0_65) uu____8762))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8786 = lhs in
          match uu____8786 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8809 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____8809 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8835 =
                        let uu____8861 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____8861) in
                      Some uu____8835
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____8944 =
                           let uu____8948 =
                             let uu____8949 = FStar_Syntax_Subst.compress k in
                             uu____8949.FStar_Syntax_Syntax.n in
                           (uu____8948, args) in
                         match uu____8944 with
                         | (uu____8956,[]) ->
                             let uu____8958 =
                               let uu____8964 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____8964) in
                             Some uu____8958
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____8975,uu____8976) ->
                             let uu____8987 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____8987 with
                              | (uv1,uv_args) ->
                                  let uu____9016 =
                                    let uu____9017 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9017.FStar_Syntax_Syntax.n in
                                  (match uu____9016 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9024) ->
                                       let uu____9037 =
                                         pat_vars env [] uv_args in
                                       (match uu____9037 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9051  ->
                                                      let uu____9052 =
                                                        let uu____9053 =
                                                          let uu____9054 =
                                                            let uu____9057 =
                                                              let uu____9058
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9058
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9057 in
                                                          fst uu____9054 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9053 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9052)) in
                                            let c1 =
                                              let uu____9064 =
                                                let uu____9065 =
                                                  let uu____9068 =
                                                    let uu____9069 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9069
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9068 in
                                                fst uu____9065 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9064 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9078 =
                                                let uu____9085 =
                                                  let uu____9091 =
                                                    let uu____9092 =
                                                      let uu____9095 =
                                                        let uu____9096 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9096
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9095 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9092 in
                                                  FStar_Util.Inl uu____9091 in
                                                Some uu____9085 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9078 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9116 -> None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9119,uu____9120)
                             ->
                             let uu____9132 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9132 with
                              | (uv1,uv_args) ->
                                  let uu____9161 =
                                    let uu____9162 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9162.FStar_Syntax_Syntax.n in
                                  (match uu____9161 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9169) ->
                                       let uu____9182 =
                                         pat_vars env [] uv_args in
                                       (match uu____9182 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9196  ->
                                                      let uu____9197 =
                                                        let uu____9198 =
                                                          let uu____9199 =
                                                            let uu____9202 =
                                                              let uu____9203
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9203
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9202 in
                                                          fst uu____9199 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9198 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9197)) in
                                            let c1 =
                                              let uu____9209 =
                                                let uu____9210 =
                                                  let uu____9213 =
                                                    let uu____9214 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9214
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9213 in
                                                fst uu____9210 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9209 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9223 =
                                                let uu____9230 =
                                                  let uu____9236 =
                                                    let uu____9237 =
                                                      let uu____9240 =
                                                        let uu____9241 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9241
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9240 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9237 in
                                                  FStar_Util.Inl uu____9236 in
                                                Some uu____9230 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9223 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9261 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9266)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____9298 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____9298
                                 (fun _0_66  -> Some _0_66)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9322 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____9322 with
                                  | (args1,rest) ->
                                      let uu____9340 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____9340 with
                                       | (xs2,c2) ->
                                           let uu____9348 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____9348
                                             (fun uu____9359  ->
                                                match uu____9359 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9381 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____9381 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____9429 =
                                        let uu____9432 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9432 in
                                      FStar_All.pipe_right uu____9429
                                        (fun _0_67  -> Some _0_67))
                         | uu____9440 ->
                             let uu____9444 =
                               let uu____9445 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____9446 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____9447 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9445 uu____9446 uu____9447 in
                             failwith uu____9444 in
                       let uu____9451 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____9451
                         (fun uu____9479  ->
                            match uu____9479 with
                            | (xs1,c1) ->
                                let uu____9507 =
                                  let uu____9530 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9530) in
                                Some uu____9507)) in
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
                     let uu____9602 = imitate orig env wl1 st in
                     match uu____9602 with
                     | Failed uu____9607 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9613 = project orig env wl1 i st in
                      match uu____9613 with
                      | None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some (Failed uu____9620) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____9634 = FStar_Syntax_Util.head_and_args t21 in
                match uu____9634 with
                | (hd1,uu____9645) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9660 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9668 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9669 -> true
                     | uu____9684 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____9687 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____9687
                         then true
                         else
                           ((let uu____9690 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____9690
                             then
                               let uu____9691 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9691
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9699 =
                    let uu____9702 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____9702 FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____9699 FStar_Syntax_Free.names in
                let uu____9733 = FStar_Util.set_is_empty fvs_hd in
                if uu____9733
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____9742 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____9742 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9750 =
                            let uu____9751 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____9751 in
                          giveup_or_defer1 orig uu____9750
                        else
                          (let uu____9753 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____9753
                           then
                             let uu____9754 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____9754
                              then
                                let uu____9755 = subterms args_lhs in
                                imitate' orig env wl1 uu____9755
                              else
                                ((let uu____9759 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____9759
                                  then
                                    let uu____9760 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____9761 = names_to_string fvs1 in
                                    let uu____9762 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9760 uu____9761 uu____9762
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9767 ->
                                        let uu____9768 = sn_binders env vars in
                                        u_abs k_uv uu____9768 t21 in
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
                               (let uu____9777 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____9777
                                then
                                  ((let uu____9779 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____9779
                                    then
                                      let uu____9780 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____9781 = names_to_string fvs1 in
                                      let uu____9782 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9780 uu____9781 uu____9782
                                    else ());
                                   (let uu____9784 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9784
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
                     (let uu____9798 =
                        let uu____9799 = FStar_Syntax_Free.names t1 in
                        check_head uu____9799 t2 in
                      if uu____9798
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____9803 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____9803
                          then
                            let uu____9804 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9804
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9807 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9807 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9852 =
               match uu____9852 with
               | (t,u,k,args) ->
                   let uu____9882 = FStar_Syntax_Util.arrow_formals k in
                   (match uu____9882 with
                    | (all_formals,uu____9893) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____9985  ->
                                        match uu____9985 with
                                        | (x,imp) ->
                                            let uu____9992 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____9992, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____10000 = FStar_Syntax_Util.type_u () in
                                match uu____10000 with
                                | (t1,uu____10004) ->
                                    let uu____10005 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    fst uu____10005 in
                              let uu____10008 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____10008 with
                               | (t',tm_u1) ->
                                   let uu____10015 = destruct_flex_t t' in
                                   (match uu____10015 with
                                    | (uu____10035,u1,k1,uu____10038) ->
                                        let sol =
                                          let uu____10066 =
                                            let uu____10071 =
                                              u_abs k all_formals t' in
                                            ((u, k), uu____10071) in
                                          TERM uu____10066 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k1, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10131 = pat_var_opt env pat_args hd1 in
                              (match uu____10131 with
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
                                              (fun uu____10160  ->
                                                 match uu____10160 with
                                                 | (x,uu____10164) ->
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
                                      let uu____10170 =
                                        let uu____10171 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____10171 in
                                      if uu____10170
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10175 =
                                           FStar_Util.set_add (fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10175 formals1
                                           tl1)))
                          | uu____10181 -> failwith "Impossible" in
                        let uu____10192 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____10192 all_formals args) in
             let solve_both_pats wl1 uu____10232 uu____10233 r =
               match (uu____10232, uu____10233) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10347 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____10347
                   then
                     let uu____10348 = solve_prob orig None [] wl1 in
                     solve env uu____10348
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____10363 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____10363
                       then
                         let uu____10364 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____10365 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____10366 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____10367 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____10368 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10364 uu____10365 uu____10366 uu____10367
                           uu____10368
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____10416 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____10416 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10429 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____10429 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10461 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10461 in
                                  let uu____10464 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____10464 k3)
                           else
                             (let uu____10467 =
                                let uu____10468 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____10469 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____10470 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10468 uu____10469 uu____10470 in
                              failwith uu____10467) in
                       let uu____10471 =
                         let uu____10477 =
                           let uu____10485 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____10485 in
                         match uu____10477 with
                         | (bs,k1') ->
                             let uu____10503 =
                               let uu____10511 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____10511 in
                             (match uu____10503 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____10532 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_68  ->
                                         FStar_TypeChecker_Common.TProb _0_68)
                                      uu____10532 in
                                  let uu____10537 =
                                    let uu____10540 =
                                      let uu____10541 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____10541.FStar_Syntax_Syntax.n in
                                    let uu____10544 =
                                      let uu____10545 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____10545.FStar_Syntax_Syntax.n in
                                    (uu____10540, uu____10544) in
                                  (match uu____10537 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10553,uu____10554) ->
                                       (k1', [sub_prob])
                                   | (uu____10558,FStar_Syntax_Syntax.Tm_type
                                      uu____10559) -> (k2', [sub_prob])
                                   | uu____10563 ->
                                       let uu____10566 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____10566 with
                                        | (t,uu____10575) ->
                                            let uu____10576 = new_uvar r zs t in
                                            (match uu____10576 with
                                             | (k_zs,uu____10585) ->
                                                 let kprob =
                                                   let uu____10587 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_69  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_69) uu____10587 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____10471 with
                       | (k_u',sub_probs) ->
                           let uu____10601 =
                             let uu____10609 =
                               let uu____10610 = new_uvar r zs k_u' in
                               FStar_All.pipe_left FStar_Pervasives.fst
                                 uu____10610 in
                             let uu____10615 =
                               let uu____10618 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____10618 in
                             let uu____10621 =
                               let uu____10624 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____10624 in
                             (uu____10609, uu____10615, uu____10621) in
                           (match uu____10601 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____10643 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____10643 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____10655 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____10655
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____10659 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____10659 with
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
             let solve_one_pat uu____10691 uu____10692 =
               match (uu____10691, uu____10692) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10756 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____10756
                     then
                       let uu____10757 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10758 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10757 uu____10758
                     else ());
                    (let uu____10760 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____10760
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10767  ->
                              fun uu____10768  ->
                                match (uu____10767, uu____10768) with
                                | ((a,uu____10778),(t21,uu____10780)) ->
                                    let uu____10785 =
                                      let uu____10788 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____10788
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____10785
                                      (fun _0_70  ->
                                         FStar_TypeChecker_Common.TProb _0_70))
                           xs args2 in
                       let guard =
                         let uu____10792 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____10792 in
                       let wl1 = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____10802 = occurs_check env wl (u1, k1) t21 in
                        match uu____10802 with
                        | (occurs_ok,uu____10807) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____10812 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____10812
                            then
                              let sol =
                                let uu____10814 =
                                  let uu____10819 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____10819) in
                                TERM uu____10814 in
                              let wl1 = solve_prob orig None [sol] wl in
                              solve env wl1
                            else
                              (let uu____10824 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____10824
                               then
                                 let uu____10825 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____10825 with
                                 | (sol,(uu____10835,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____10845 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____10845
                                       then
                                         let uu____10846 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10846
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10851 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____10853 = lhs in
             match uu____10853 with
             | (t1,u1,k1,args1) ->
                 let uu____10858 = rhs in
                 (match uu____10858 with
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
                       | uu____10884 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____10890 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____10890 with
                              | (sol,uu____10897) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____10900 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____10900
                                    then
                                      let uu____10901 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____10901
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____10906 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____10908 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____10908
        then
          let uu____10909 = solve_prob orig None [] wl in
          solve env uu____10909
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____10913 = FStar_Util.physical_equality t1 t2 in
           if uu____10913
           then
             let uu____10914 = solve_prob orig None [] wl in
             solve env uu____10914
           else
             ((let uu____10917 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____10917
               then
                 let uu____10918 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____10918
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____10921,uu____10922) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____10923,FStar_Syntax_Syntax.Tm_bvar uu____10924) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___131_10964 =
                     match uu___131_10964 with
                     | [] -> c
                     | bs ->
                         let uu____10978 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c)) None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____10978 in
                   let uu____10988 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____10988 with
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
                                   let uu____11074 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____11074
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____11076 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_71  ->
                                      FStar_TypeChecker_Common.CProb _0_71)
                                   uu____11076))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___132_11153 =
                     match uu___132_11153 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l)) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____11188 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____11188 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11271 =
                                   let uu____11274 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____11275 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____11274
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11275 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_72  ->
                                      FStar_TypeChecker_Common.TProb _0_72)
                                   uu____11271))
               | (FStar_Syntax_Syntax.Tm_abs uu____11278,uu____11279) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11302 -> true
                     | uu____11317 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11345 =
                     let uu____11356 = maybe_eta t1 in
                     let uu____11361 = maybe_eta t2 in
                     (uu____11356, uu____11361) in
                   (match uu____11345 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___165_11392 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___165_11392.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___165_11392.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___165_11392.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___165_11392.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___165_11392.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___165_11392.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___165_11392.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___165_11392.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11411 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11411
                        then
                          let uu____11412 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11412 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11433 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11433
                        then
                          let uu____11434 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11434 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11439 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11450,FStar_Syntax_Syntax.Tm_abs uu____11451) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11474 -> true
                     | uu____11489 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11517 =
                     let uu____11528 = maybe_eta t1 in
                     let uu____11533 = maybe_eta t2 in
                     (uu____11528, uu____11533) in
                   (match uu____11517 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___165_11564 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___165_11564.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___165_11564.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___165_11564.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___165_11564.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___165_11564.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___165_11564.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___165_11564.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___165_11564.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11583 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11583
                        then
                          let uu____11584 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11584 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11605 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11605
                        then
                          let uu____11606 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11606 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11611 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11622,FStar_Syntax_Syntax.Tm_refine uu____11623) ->
                   let uu____11632 = as_refinement env wl t1 in
                   (match uu____11632 with
                    | (x1,phi1) ->
                        let uu____11637 = as_refinement env wl t2 in
                        (match uu____11637 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11643 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_73  ->
                                    FStar_TypeChecker_Common.TProb _0_73)
                                 uu____11643 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____11676 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____11676
                                 (guard_on_element wl problem x11) in
                             let fallback uu____11680 =
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
                                 let uu____11686 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____11686 impl in
                               let wl1 = solve_prob orig (Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11693 =
                                   let uu____11696 =
                                     let uu____11697 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____11697 :: (p_scope orig) in
                                   mk_problem uu____11696 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_74  ->
                                      FStar_TypeChecker_Common.TProb _0_74)
                                   uu____11693 in
                               let uu____11700 =
                                 solve env1
                                   (let uu___166_11701 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___166_11701.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___166_11701.smt_ok);
                                      tcenv = (uu___166_11701.tcenv)
                                    }) in
                               (match uu____11700 with
                                | Failed uu____11705 -> fallback ()
                                | Success uu____11708 ->
                                    let guard =
                                      let uu____11712 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives.fst in
                                      let uu____11715 =
                                        let uu____11716 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives.fst in
                                        FStar_All.pipe_right uu____11716
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____11712
                                        uu____11715 in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl2 =
                                      let uu___167_11723 = wl1 in
                                      {
                                        attempting =
                                          (uu___167_11723.attempting);
                                        wl_deferred =
                                          (uu___167_11723.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___167_11723.defer_ok);
                                        smt_ok = (uu___167_11723.smt_ok);
                                        tcenv = (uu___167_11723.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11725,FStar_Syntax_Syntax.Tm_uvar uu____11726) ->
                   let uu____11743 = destruct_flex_t t1 in
                   let uu____11744 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11743 uu____11744
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11745;
                     FStar_Syntax_Syntax.tk = uu____11746;
                     FStar_Syntax_Syntax.pos = uu____11747;
                     FStar_Syntax_Syntax.vars = uu____11748;_},uu____11749),FStar_Syntax_Syntax.Tm_uvar
                  uu____11750) ->
                   let uu____11781 = destruct_flex_t t1 in
                   let uu____11782 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11781 uu____11782
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11783,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11784;
                     FStar_Syntax_Syntax.tk = uu____11785;
                     FStar_Syntax_Syntax.pos = uu____11786;
                     FStar_Syntax_Syntax.vars = uu____11787;_},uu____11788))
                   ->
                   let uu____11819 = destruct_flex_t t1 in
                   let uu____11820 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11819 uu____11820
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11821;
                     FStar_Syntax_Syntax.tk = uu____11822;
                     FStar_Syntax_Syntax.pos = uu____11823;
                     FStar_Syntax_Syntax.vars = uu____11824;_},uu____11825),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11826;
                     FStar_Syntax_Syntax.tk = uu____11827;
                     FStar_Syntax_Syntax.pos = uu____11828;
                     FStar_Syntax_Syntax.vars = uu____11829;_},uu____11830))
                   ->
                   let uu____11875 = destruct_flex_t t1 in
                   let uu____11876 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11875 uu____11876
               | (FStar_Syntax_Syntax.Tm_uvar uu____11877,uu____11878) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11887 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11887 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11891;
                     FStar_Syntax_Syntax.tk = uu____11892;
                     FStar_Syntax_Syntax.pos = uu____11893;
                     FStar_Syntax_Syntax.vars = uu____11894;_},uu____11895),uu____11896)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11919 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11919 t2 wl
               | (uu____11923,FStar_Syntax_Syntax.Tm_uvar uu____11924) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____11933,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11934;
                     FStar_Syntax_Syntax.tk = uu____11935;
                     FStar_Syntax_Syntax.pos = uu____11936;
                     FStar_Syntax_Syntax.vars = uu____11937;_},uu____11938))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11961,FStar_Syntax_Syntax.Tm_type uu____11962) ->
                   solve_t' env
                     (let uu___168_11971 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_11971.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_11971.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_11971.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_11971.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_11971.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_11971.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_11971.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_11971.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_11971.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11972;
                     FStar_Syntax_Syntax.tk = uu____11973;
                     FStar_Syntax_Syntax.pos = uu____11974;
                     FStar_Syntax_Syntax.vars = uu____11975;_},uu____11976),FStar_Syntax_Syntax.Tm_type
                  uu____11977) ->
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
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12001,FStar_Syntax_Syntax.Tm_arrow uu____12002) ->
                   solve_t' env
                     (let uu___168_12018 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_12018.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_12018.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_12018.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_12018.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_12018.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_12018.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_12018.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_12018.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_12018.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12019;
                     FStar_Syntax_Syntax.tk = uu____12020;
                     FStar_Syntax_Syntax.pos = uu____12021;
                     FStar_Syntax_Syntax.vars = uu____12022;_},uu____12023),FStar_Syntax_Syntax.Tm_arrow
                  uu____12024) ->
                   solve_t' env
                     (let uu___168_12054 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_12054.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_12054.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_12054.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_12054.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_12054.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_12054.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_12054.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_12054.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_12054.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____12055,uu____12056) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12067 =
                        let uu____12068 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12068 in
                      if uu____12067
                      then
                        let uu____12069 =
                          FStar_All.pipe_left
                            (fun _0_75  ->
                               FStar_TypeChecker_Common.TProb _0_75)
                            (let uu___169_12072 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_12072.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_12072.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_12072.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_12072.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_12072.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___169_12072.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_12072.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_12072.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_12072.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12073 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12069 uu____12073 t2
                          wl
                      else
                        (let uu____12078 = base_and_refinement env wl t2 in
                         match uu____12078 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12108 =
                                    FStar_All.pipe_left
                                      (fun _0_76  ->
                                         FStar_TypeChecker_Common.TProb _0_76)
                                      (let uu___170_12111 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___170_12111.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___170_12111.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___170_12111.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___170_12111.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___170_12111.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___170_12111.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___170_12111.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___170_12111.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___170_12111.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12112 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12108
                                    uu____12112 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___171_12127 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___171_12127.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___171_12127.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12130 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_77  ->
                                         FStar_TypeChecker_Common.TProb _0_77)
                                      uu____12130 in
                                  let guard =
                                    let uu____12138 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12138
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12144;
                     FStar_Syntax_Syntax.tk = uu____12145;
                     FStar_Syntax_Syntax.pos = uu____12146;
                     FStar_Syntax_Syntax.vars = uu____12147;_},uu____12148),uu____12149)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12174 =
                        let uu____12175 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12175 in
                      if uu____12174
                      then
                        let uu____12176 =
                          FStar_All.pipe_left
                            (fun _0_78  ->
                               FStar_TypeChecker_Common.TProb _0_78)
                            (let uu___169_12179 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_12179.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_12179.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_12179.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_12179.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_12179.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___169_12179.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_12179.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_12179.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_12179.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12180 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12176 uu____12180 t2
                          wl
                      else
                        (let uu____12185 = base_and_refinement env wl t2 in
                         match uu____12185 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12215 =
                                    FStar_All.pipe_left
                                      (fun _0_79  ->
                                         FStar_TypeChecker_Common.TProb _0_79)
                                      (let uu___170_12218 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___170_12218.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___170_12218.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___170_12218.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___170_12218.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___170_12218.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___170_12218.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___170_12218.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___170_12218.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___170_12218.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12219 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12215
                                    uu____12219 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___171_12234 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___171_12234.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___171_12234.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12237 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_80  ->
                                         FStar_TypeChecker_Common.TProb _0_80)
                                      uu____12237 in
                                  let guard =
                                    let uu____12245 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12245
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12251,FStar_Syntax_Syntax.Tm_uvar uu____12252) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12262 = base_and_refinement env wl t1 in
                      match uu____12262 with
                      | (t_base,uu____12273) ->
                          solve_t env
                            (let uu___172_12288 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___172_12288.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___172_12288.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___172_12288.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___172_12288.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___172_12288.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___172_12288.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___172_12288.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___172_12288.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12291,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12292;
                     FStar_Syntax_Syntax.tk = uu____12293;
                     FStar_Syntax_Syntax.pos = uu____12294;
                     FStar_Syntax_Syntax.vars = uu____12295;_},uu____12296))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12320 = base_and_refinement env wl t1 in
                      match uu____12320 with
                      | (t_base,uu____12331) ->
                          solve_t env
                            (let uu___172_12346 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___172_12346.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___172_12346.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___172_12346.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___172_12346.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___172_12346.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___172_12346.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___172_12346.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___172_12346.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12349,uu____12350) ->
                   let t21 =
                     let uu____12358 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____12358 in
                   solve_t env
                     (let uu___173_12371 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_12371.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___173_12371.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___173_12371.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___173_12371.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_12371.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_12371.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_12371.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_12371.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_12371.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12372,FStar_Syntax_Syntax.Tm_refine uu____12373) ->
                   let t11 =
                     let uu____12381 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____12381 in
                   solve_t env
                     (let uu___174_12394 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_12394.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___174_12394.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___174_12394.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___174_12394.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_12394.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_12394.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_12394.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_12394.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_12394.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12397,uu____12398) ->
                   let head1 =
                     let uu____12417 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12417 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12448 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12448 FStar_Pervasives.fst in
                   let uu____12476 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12476
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12485 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12485
                      then
                        let guard =
                          let uu____12492 =
                            let uu____12493 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12493 = FStar_Syntax_Util.Equal in
                          if uu____12492
                          then None
                          else
                            (let uu____12496 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_81  -> Some _0_81)
                               uu____12496) in
                        let uu____12498 = solve_prob orig guard [] wl in
                        solve env uu____12498
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12501,uu____12502) ->
                   let head1 =
                     let uu____12510 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12510 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12541 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12541 FStar_Pervasives.fst in
                   let uu____12569 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12569
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12578 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12578
                      then
                        let guard =
                          let uu____12585 =
                            let uu____12586 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12586 = FStar_Syntax_Util.Equal in
                          if uu____12585
                          then None
                          else
                            (let uu____12589 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_82  -> Some _0_82)
                               uu____12589) in
                        let uu____12591 = solve_prob orig guard [] wl in
                        solve env uu____12591
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12594,uu____12595) ->
                   let head1 =
                     let uu____12599 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12599 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12630 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12630 FStar_Pervasives.fst in
                   let uu____12658 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12658
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12667 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12667
                      then
                        let guard =
                          let uu____12674 =
                            let uu____12675 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12675 = FStar_Syntax_Util.Equal in
                          if uu____12674
                          then None
                          else
                            (let uu____12678 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_83  -> Some _0_83)
                               uu____12678) in
                        let uu____12680 = solve_prob orig guard [] wl in
                        solve env uu____12680
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12683,uu____12684) ->
                   let head1 =
                     let uu____12688 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12688 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12719 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12719 FStar_Pervasives.fst in
                   let uu____12747 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12747
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12756 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12756
                      then
                        let guard =
                          let uu____12763 =
                            let uu____12764 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12764 = FStar_Syntax_Util.Equal in
                          if uu____12763
                          then None
                          else
                            (let uu____12767 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_84  -> Some _0_84)
                               uu____12767) in
                        let uu____12769 = solve_prob orig guard [] wl in
                        solve env uu____12769
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____12772,uu____12773) ->
                   let head1 =
                     let uu____12777 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12777 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12808 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12808 FStar_Pervasives.fst in
                   let uu____12836 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12836
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12845 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12845
                      then
                        let guard =
                          let uu____12852 =
                            let uu____12853 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12853 = FStar_Syntax_Util.Equal in
                          if uu____12852
                          then None
                          else
                            (let uu____12856 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_85  -> Some _0_85)
                               uu____12856) in
                        let uu____12858 = solve_prob orig guard [] wl in
                        solve env uu____12858
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____12861,uu____12862) ->
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
                             FStar_All.pipe_left (fun _0_86  -> Some _0_86)
                               uu____12954) in
                        let uu____12956 = solve_prob orig guard [] wl in
                        solve env uu____12956
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12959,FStar_Syntax_Syntax.Tm_match uu____12960) ->
                   let head1 =
                     let uu____12979 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12979 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13010 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13010 FStar_Pervasives.fst in
                   let uu____13038 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13038
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13047 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13047
                      then
                        let guard =
                          let uu____13054 =
                            let uu____13055 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13055 = FStar_Syntax_Util.Equal in
                          if uu____13054
                          then None
                          else
                            (let uu____13058 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_87  -> Some _0_87)
                               uu____13058) in
                        let uu____13060 = solve_prob orig guard [] wl in
                        solve env uu____13060
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13063,FStar_Syntax_Syntax.Tm_uinst uu____13064) ->
                   let head1 =
                     let uu____13072 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13072 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13103 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13103 FStar_Pervasives.fst in
                   let uu____13131 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13131
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13140 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13140
                      then
                        let guard =
                          let uu____13147 =
                            let uu____13148 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13148 = FStar_Syntax_Util.Equal in
                          if uu____13147
                          then None
                          else
                            (let uu____13151 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_88  -> Some _0_88)
                               uu____13151) in
                        let uu____13153 = solve_prob orig guard [] wl in
                        solve env uu____13153
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13156,FStar_Syntax_Syntax.Tm_name uu____13157) ->
                   let head1 =
                     let uu____13161 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13161 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13192 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13192 FStar_Pervasives.fst in
                   let uu____13220 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13220
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13229 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13229
                      then
                        let guard =
                          let uu____13236 =
                            let uu____13237 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13237 = FStar_Syntax_Util.Equal in
                          if uu____13236
                          then None
                          else
                            (let uu____13240 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_89  -> Some _0_89)
                               uu____13240) in
                        let uu____13242 = solve_prob orig guard [] wl in
                        solve env uu____13242
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13245,FStar_Syntax_Syntax.Tm_constant uu____13246) ->
                   let head1 =
                     let uu____13250 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13250 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13281 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13281 FStar_Pervasives.fst in
                   let uu____13309 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13309
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13318 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13318
                      then
                        let guard =
                          let uu____13325 =
                            let uu____13326 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13326 = FStar_Syntax_Util.Equal in
                          if uu____13325
                          then None
                          else
                            (let uu____13329 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_90  -> Some _0_90)
                               uu____13329) in
                        let uu____13331 = solve_prob orig guard [] wl in
                        solve env uu____13331
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13334,FStar_Syntax_Syntax.Tm_fvar uu____13335) ->
                   let head1 =
                     let uu____13339 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13339 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13370 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13370 FStar_Pervasives.fst in
                   let uu____13398 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13398
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13407 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13407
                      then
                        let guard =
                          let uu____13414 =
                            let uu____13415 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13415 = FStar_Syntax_Util.Equal in
                          if uu____13414
                          then None
                          else
                            (let uu____13418 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_91  -> Some _0_91)
                               uu____13418) in
                        let uu____13420 = solve_prob orig guard [] wl in
                        solve env uu____13420
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13423,FStar_Syntax_Syntax.Tm_app uu____13424) ->
                   let head1 =
                     let uu____13437 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13437 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13468 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13468 FStar_Pervasives.fst in
                   let uu____13496 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13496
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13505 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13505
                      then
                        let guard =
                          let uu____13512 =
                            let uu____13513 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13513 = FStar_Syntax_Util.Equal in
                          if uu____13512
                          then None
                          else
                            (let uu____13516 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_92  -> Some _0_92)
                               uu____13516) in
                        let uu____13518 = solve_prob orig guard [] wl in
                        solve env uu____13518
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13522,uu____13523),uu____13524) ->
                   solve_t' env
                     (let uu___175_13553 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_13553.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_13553.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_13553.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_13553.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_13553.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_13553.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_13553.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_13553.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_13553.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13556,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13558,uu____13559)) ->
                   solve_t' env
                     (let uu___176_13588 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_13588.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___176_13588.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___176_13588.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___176_13588.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_13588.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_13588.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_13588.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_13588.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_13588.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13589,uu____13590) ->
                   let uu____13598 =
                     let uu____13599 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13600 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13599
                       uu____13600 in
                   failwith uu____13598
               | (FStar_Syntax_Syntax.Tm_meta uu____13601,uu____13602) ->
                   let uu____13607 =
                     let uu____13608 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13609 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13608
                       uu____13609 in
                   failwith uu____13607
               | (FStar_Syntax_Syntax.Tm_delayed uu____13610,uu____13611) ->
                   let uu____13632 =
                     let uu____13633 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13634 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13633
                       uu____13634 in
                   failwith uu____13632
               | (uu____13635,FStar_Syntax_Syntax.Tm_meta uu____13636) ->
                   let uu____13641 =
                     let uu____13642 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13643 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13642
                       uu____13643 in
                   failwith uu____13641
               | (uu____13644,FStar_Syntax_Syntax.Tm_delayed uu____13645) ->
                   let uu____13666 =
                     let uu____13667 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13668 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13667
                       uu____13668 in
                   failwith uu____13666
               | (uu____13669,FStar_Syntax_Syntax.Tm_let uu____13670) ->
                   let uu____13678 =
                     let uu____13679 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13680 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13679
                       uu____13680 in
                   failwith uu____13678
               | uu____13681 -> giveup env "head tag mismatch" orig)))
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
          (let uu____13713 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____13713
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____13721  ->
                  fun uu____13722  ->
                    match (uu____13721, uu____13722) with
                    | ((a1,uu____13732),(a2,uu____13734)) ->
                        let uu____13739 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_93  -> FStar_TypeChecker_Common.TProb _0_93)
                          uu____13739)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____13745 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p) FStar_Pervasives.fst)
                 sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____13745 in
           let wl1 = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____13765 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____13772)::[] -> wp1
              | uu____13785 ->
                  let uu____13791 =
                    let uu____13792 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____13792 in
                  failwith uu____13791 in
            let uu____13795 =
              let uu____13801 =
                let uu____13802 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____13802 in
              [uu____13801] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____13795;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____13803 = lift_c1 () in solve_eq uu____13803 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___133_13807  ->
                       match uu___133_13807 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____13808 -> false)) in
             let uu____13809 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____13833)::uu____13834,(wp2,uu____13836)::uu____13837)
                   -> (wp1, wp2)
               | uu____13878 ->
                   let uu____13891 =
                     let uu____13892 =
                       let uu____13895 =
                         let uu____13896 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____13897 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____13896 uu____13897 in
                       (uu____13895, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____13892 in
                   raise uu____13891 in
             match uu____13809 with
             | (wpc1,wpc2) ->
                 let uu____13914 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____13914
                 then
                   let uu____13917 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env uu____13917 wl
                 else
                   (let uu____13921 =
                      let uu____13925 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____13925 in
                    match uu____13921 with
                    | (c2_decl,qualifiers) ->
                        let uu____13937 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____13937
                        then
                          let c1_repr =
                            let uu____13940 =
                              let uu____13941 =
                                let uu____13942 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____13942 in
                              let uu____13943 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13941 uu____13943 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13940 in
                          let c2_repr =
                            let uu____13945 =
                              let uu____13946 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____13947 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13946 uu____13947 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13945 in
                          let prob =
                            let uu____13949 =
                              let uu____13952 =
                                let uu____13953 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____13954 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____13953
                                  uu____13954 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____13952 in
                            FStar_TypeChecker_Common.TProb uu____13949 in
                          let wl1 =
                            let uu____13956 =
                              let uu____13958 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives.fst in
                              Some uu____13958 in
                            solve_prob orig uu____13956 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____13965 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____13965
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____13967 =
                                     let uu____13970 =
                                       let uu____13971 =
                                         let uu____13981 =
                                           let uu____13982 =
                                             let uu____13983 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____13983] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____13982 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____13984 =
                                           let uu____13986 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____13987 =
                                             let uu____13989 =
                                               let uu____13990 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____13990 in
                                             [uu____13989] in
                                           uu____13986 :: uu____13987 in
                                         (uu____13981, uu____13984) in
                                       FStar_Syntax_Syntax.Tm_app uu____13971 in
                                     FStar_Syntax_Syntax.mk uu____13970 in
                                   uu____13967
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____14001 =
                                    let uu____14004 =
                                      let uu____14005 =
                                        let uu____14015 =
                                          let uu____14016 =
                                            let uu____14017 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____14017] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____14016 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____14018 =
                                          let uu____14020 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____14021 =
                                            let uu____14023 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____14024 =
                                              let uu____14026 =
                                                let uu____14027 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14027 in
                                              [uu____14026] in
                                            uu____14023 :: uu____14024 in
                                          uu____14020 :: uu____14021 in
                                        (uu____14015, uu____14018) in
                                      FStar_Syntax_Syntax.Tm_app uu____14005 in
                                    FStar_Syntax_Syntax.mk uu____14004 in
                                  uu____14001
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____14038 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_94  ->
                                  FStar_TypeChecker_Common.TProb _0_94)
                               uu____14038 in
                           let wl1 =
                             let uu____14044 =
                               let uu____14046 =
                                 let uu____14049 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____14049 g in
                               FStar_All.pipe_left (fun _0_95  -> Some _0_95)
                                 uu____14046 in
                             solve_prob orig uu____14044 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____14059 = FStar_Util.physical_equality c1 c2 in
        if uu____14059
        then
          let uu____14060 = solve_prob orig None [] wl in
          solve env uu____14060
        else
          ((let uu____14063 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____14063
            then
              let uu____14064 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____14065 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14064
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14065
            else ());
           (let uu____14067 =
              let uu____14070 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____14071 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____14070, uu____14071) in
            match uu____14067 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14075),FStar_Syntax_Syntax.Total
                    (t2,uu____14077)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14090 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14090 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14093,FStar_Syntax_Syntax.Total uu____14094) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14106),FStar_Syntax_Syntax.Total
                    (t2,uu____14108)) ->
                     let uu____14121 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14121 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14125),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14127)) ->
                     let uu____14140 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14140 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14144),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14146)) ->
                     let uu____14159 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14159 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14162,FStar_Syntax_Syntax.Comp uu____14163) ->
                     let uu____14169 =
                       let uu___177_14172 = problem in
                       let uu____14175 =
                         let uu____14176 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14176 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14172.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14175;
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14172.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___177_14172.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___177_14172.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14172.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14172.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14172.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14172.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14172.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14169 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14177,FStar_Syntax_Syntax.Comp uu____14178) ->
                     let uu____14184 =
                       let uu___177_14187 = problem in
                       let uu____14190 =
                         let uu____14191 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14191 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14187.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14190;
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14187.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___177_14187.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___177_14187.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14187.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14187.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14187.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14187.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14187.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14184 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14192,FStar_Syntax_Syntax.GTotal uu____14193) ->
                     let uu____14199 =
                       let uu___178_14202 = problem in
                       let uu____14205 =
                         let uu____14206 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14206 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14202.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___178_14202.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14202.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14205;
                         FStar_TypeChecker_Common.element =
                           (uu___178_14202.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14202.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14202.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14202.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14202.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14202.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14199 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14207,FStar_Syntax_Syntax.Total uu____14208) ->
                     let uu____14214 =
                       let uu___178_14217 = problem in
                       let uu____14220 =
                         let uu____14221 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14221 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14217.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___178_14217.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14217.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14220;
                         FStar_TypeChecker_Common.element =
                           (uu___178_14217.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14217.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14217.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14217.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14217.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14217.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14214 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14222,FStar_Syntax_Syntax.Comp uu____14223) ->
                     let uu____14224 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____14224
                     then
                       let uu____14225 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type" in
                       solve_t env uu____14225 wl
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
                           (let uu____14235 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____14235
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14237 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____14237 with
                            | None  ->
                                let uu____14239 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14240 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____14240) in
                                if uu____14239
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
                                  (let uu____14243 =
                                     let uu____14244 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____14245 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14244 uu____14245 in
                                   giveup env uu____14243 orig)
                            | Some edge -> solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14250 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14266  ->
              match uu____14266 with
              | (uu____14273,uu____14274,u,uu____14276,uu____14277,uu____14278)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____14250 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14296 =
        FStar_All.pipe_right (fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____14296 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____14306 =
        FStar_All.pipe_right (snd ineqs)
          (FStar_List.map
             (fun uu____14318  ->
                match uu____14318 with
                | (u1,u2) ->
                    let uu____14323 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____14324 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____14323 uu____14324)) in
      FStar_All.pipe_right uu____14306 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14336,[])) -> "{}"
      | uu____14349 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14359 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____14359
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____14362 =
              FStar_List.map
                (fun uu____14366  ->
                   match uu____14366 with
                   | (uu____14369,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____14362 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____14373 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14373 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14411 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____14411
    then
      let uu____14412 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____14413 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14412
        (rel_to_string rel) uu____14413
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
            let uu____14433 =
              let uu____14435 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_96  -> Some _0_96) uu____14435 in
            FStar_Syntax_Syntax.new_bv uu____14433 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____14441 =
              let uu____14443 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_97  -> Some _0_97) uu____14443 in
            let uu____14445 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____14441 uu____14445 in
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
          let uu____14468 = FStar_Options.eager_inference () in
          if uu____14468
          then
            let uu___179_14469 = probs in
            {
              attempting = (uu___179_14469.attempting);
              wl_deferred = (uu___179_14469.wl_deferred);
              ctr = (uu___179_14469.ctr);
              defer_ok = false;
              smt_ok = (uu___179_14469.smt_ok);
              tcenv = (uu___179_14469.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Syntax_Unionfind.rollback tx;
             (let uu____14480 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____14480
              then
                let uu____14481 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____14481
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
          ((let uu____14491 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____14491
            then
              let uu____14492 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14492
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____14496 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____14496
             then
               let uu____14497 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14497
             else ());
            (let f2 =
               let uu____14500 =
                 let uu____14501 = FStar_Syntax_Util.unmeta f1 in
                 uu____14501.FStar_Syntax_Syntax.n in
               match uu____14500 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14505 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___180_14506 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___180_14506.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___180_14506.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___180_14506.FStar_TypeChecker_Env.implicits)
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
            let uu____14521 =
              let uu____14522 =
                let uu____14523 =
                  let uu____14524 =
                    FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____14524
                    (fun _0_98  -> FStar_TypeChecker_Common.NonTrivial _0_98) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14523;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____14522 in
            FStar_All.pipe_left (fun _0_99  -> Some _0_99) uu____14521
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____14557 =
        let uu____14558 =
          let uu____14559 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
          FStar_All.pipe_right uu____14559
            (fun _0_100  -> FStar_TypeChecker_Common.NonTrivial _0_100) in
        {
          FStar_TypeChecker_Env.guard_f = uu____14558;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      Some uu____14557
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
          (let uu____14585 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14585
           then
             let uu____14586 = FStar_Syntax_Print.term_to_string t1 in
             let uu____14587 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14586
               uu____14587
           else ());
          (let prob =
             let uu____14590 =
               let uu____14593 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____14593 in
             FStar_All.pipe_left
               (fun _0_101  -> FStar_TypeChecker_Common.TProb _0_101)
               uu____14590 in
           let g =
             let uu____14598 =
               let uu____14600 = singleton' env prob smt_ok in
               solve_and_commit env uu____14600 (fun uu____14601  -> None) in
             FStar_All.pipe_left (with_guard env prob) uu____14598 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14615 = try_teq true env t1 t2 in
        match uu____14615 with
        | None  ->
            let uu____14617 =
              let uu____14618 =
                let uu____14621 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                let uu____14622 = FStar_TypeChecker_Env.get_range env in
                (uu____14621, uu____14622) in
              FStar_Errors.Error uu____14618 in
            raise uu____14617
        | Some g ->
            ((let uu____14625 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____14625
              then
                let uu____14626 = FStar_Syntax_Print.term_to_string t1 in
                let uu____14627 = FStar_Syntax_Print.term_to_string t2 in
                let uu____14628 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14626
                  uu____14627 uu____14628
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
          (let uu____14644 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14644
           then
             let uu____14645 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____14646 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14645
               uu____14646
           else ());
          (let uu____14648 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____14648 with
           | (prob,x) ->
               let g =
                 let uu____14656 =
                   let uu____14658 = singleton' env prob smt_ok in
                   solve_and_commit env uu____14658
                     (fun uu____14659  -> None) in
                 FStar_All.pipe_left (with_guard env prob) uu____14656 in
               ((let uu____14665 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____14665
                 then
                   let uu____14666 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____14667 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____14668 =
                     let uu____14669 = FStar_Util.must g in
                     guard_to_string env uu____14669 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14666 uu____14667 uu____14668
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
          let uu____14693 = FStar_TypeChecker_Env.get_range env in
          let uu____14694 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.err uu____14693 uu____14694
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____14706 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____14706
         then
           let uu____14707 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____14708 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____14707
             uu____14708
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____14713 =
             let uu____14716 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None uu____14716 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_102  -> FStar_TypeChecker_Common.CProb _0_102)
             uu____14713 in
         let uu____14719 =
           let uu____14721 = singleton env prob in
           solve_and_commit env uu____14721 (fun uu____14722  -> None) in
         FStar_All.pipe_left (with_guard env prob) uu____14719)
let solve_universe_inequalities':
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____14741  ->
        match uu____14741 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____14766 =
                 let uu____14767 =
                   let uu____14770 =
                     let uu____14771 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____14772 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____14771 uu____14772 in
                   let uu____14773 = FStar_TypeChecker_Env.get_range env in
                   (uu____14770, uu____14773) in
                 FStar_Errors.Error uu____14767 in
               raise uu____14766) in
            let equiv1 v1 v' =
              let uu____14781 =
                let uu____14784 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____14785 = FStar_Syntax_Subst.compress_univ v' in
                (uu____14784, uu____14785) in
              match uu____14781 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____14792 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____14806 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____14806 with
                      | FStar_Syntax_Syntax.U_unif uu____14810 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____14821  ->
                                    match uu____14821 with
                                    | (u,v') ->
                                        let uu____14827 = equiv1 v1 v' in
                                        if uu____14827
                                        then
                                          let uu____14829 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____14829 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____14839 -> [])) in
            let uu____14842 =
              let wl =
                let uu___181_14845 = empty_worklist env in
                {
                  attempting = (uu___181_14845.attempting);
                  wl_deferred = (uu___181_14845.wl_deferred);
                  ctr = (uu___181_14845.ctr);
                  defer_ok = false;
                  smt_ok = (uu___181_14845.smt_ok);
                  tcenv = (uu___181_14845.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____14852  ->
                      match uu____14852 with
                      | (lb,v1) ->
                          let uu____14857 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____14857 with
                           | USolved wl1 -> ()
                           | uu____14859 -> fail lb v1))) in
            let rec check_ineq uu____14865 =
              match uu____14865 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____14872) -> true
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
                      uu____14883,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____14885,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____14890) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____14894,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____14899 -> false) in
            let uu____14902 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____14908  ->
                      match uu____14908 with
                      | (u,v1) ->
                          let uu____14913 = check_ineq (u, v1) in
                          if uu____14913
                          then true
                          else
                            ((let uu____14916 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____14916
                              then
                                let uu____14917 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____14918 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____14917
                                  uu____14918
                              else ());
                             false))) in
            if uu____14902
            then ()
            else
              ((let uu____14922 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____14922
                then
                  ((let uu____14924 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____14924);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____14930 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____14930))
                else ());
               (let uu____14936 =
                  let uu____14937 =
                    let uu____14940 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____14940) in
                  FStar_Errors.Error uu____14937 in
                raise uu____14936))
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
      let fail uu____14973 =
        match uu____14973 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____14983 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____14983
       then
         let uu____14984 = wl_to_string wl in
         let uu____14985 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____14984 uu____14985
       else ());
      (let g1 =
         let uu____15000 = solve_and_commit env wl fail in
         match uu____15000 with
         | Some [] ->
             let uu___182_15007 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___182_15007.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___182_15007.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___182_15007.FStar_TypeChecker_Env.implicits)
             }
         | uu____15010 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___183_15013 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___183_15013.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___183_15013.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___183_15013.FStar_TypeChecker_Env.implicits)
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
            let uu___184_15039 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___184_15039.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___184_15039.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___184_15039.FStar_TypeChecker_Env.implicits)
            } in
          let uu____15040 =
            let uu____15041 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____15041 in
          if uu____15040
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15047 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____15047
                   then
                     let uu____15048 = FStar_TypeChecker_Env.get_range env in
                     let uu____15049 =
                       let uu____15050 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15050 in
                     FStar_Errors.diag uu____15048 uu____15049
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding] env vc in
                   let uu____15053 = check_trivial vc1 in
                   match uu____15053 with
                   | FStar_TypeChecker_Common.Trivial  -> Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then None
                       else
                         ((let uu____15060 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15060
                           then
                             let uu____15061 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____15062 =
                               let uu____15063 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15063 in
                             FStar_Errors.diag uu____15061 uu____15062
                           else ());
                          (let vcs =
                             let uu____15069 = FStar_Options.use_tactics () in
                             if uu____15069
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)] in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____15083  ->
                                   match uu____15083 with
                                   | (env1,goal) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify]
                                           env1 goal in
                                       let uu____15089 = check_trivial goal1 in
                                       (match uu____15089 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____15091 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____15091
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                                               ();
                                             (let uu____15096 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____15096
                                              then
                                                let uu____15097 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____15098 =
                                                  let uu____15099 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____15100 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____15099 uu____15100 in
                                                FStar_Errors.diag uu____15097
                                                  uu____15098
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
      let uu____15108 = discharge_guard' None env g false in
      match uu____15108 with
      | Some g1 -> g1
      | None  ->
          let uu____15113 =
            let uu____15114 =
              let uu____15117 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____15117) in
            FStar_Errors.Error uu____15114 in
          raise uu____15113
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15124 = discharge_guard' None env g true in
      match uu____15124 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____15136 = FStar_Syntax_Unionfind.find u in
      match uu____15136 with | None  -> true | uu____15138 -> false in
    let rec until_fixpoint acc implicits =
      let uu____15151 = acc in
      match uu____15151 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____15197 = hd1 in
               (match uu____15197 with
                | (uu____15204,env,u,tm,k,r) ->
                    let uu____15210 = unresolved u in
                    if uu____15210
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm in
                       (let uu____15228 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck") in
                        if uu____15228
                        then
                          let uu____15229 =
                            FStar_Syntax_Print.uvar_to_string u in
                          let uu____15230 =
                            FStar_Syntax_Print.term_to_string tm1 in
                          let uu____15231 =
                            FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____15229 uu____15230 uu____15231
                        else ());
                       (let uu____15233 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___185_15237 = env1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___185_15237.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___185_15237.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___185_15237.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___185_15237.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___185_15237.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___185_15237.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___185_15237.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___185_15237.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___185_15237.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___185_15237.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___185_15237.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___185_15237.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___185_15237.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___185_15237.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___185_15237.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___185_15237.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___185_15237.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___185_15237.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___185_15237.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___185_15237.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___185_15237.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___185_15237.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___185_15237.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___185_15237.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___185_15237.FStar_TypeChecker_Env.synth)
                             }) tm1 in
                        match uu____15233 with
                        | (uu____15238,uu____15239,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___186_15242 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___186_15242.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___186_15242.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___186_15242.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____15245 =
                                discharge_guard'
                                  (Some
                                     (fun uu____15249  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____15245 with
                              | Some g3 -> g3
                              | None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
    let uu___187_15264 = g in
    let uu____15265 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___187_15264.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___187_15264.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___187_15264.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____15265
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____15293 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____15293 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15300 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15300
      | (reason,uu____15302,uu____15303,e,t,r)::uu____15307 ->
          let uu____15321 =
            let uu____15322 = FStar_Syntax_Print.term_to_string t in
            let uu____15323 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format3
              "Failed to resolve implicit argument of type '%s' introduced in %s because %s"
              uu____15322 uu____15323 reason in
          FStar_Errors.err r uu____15321
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___188_15330 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___188_15330.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___188_15330.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___188_15330.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15348 = try_teq false env t1 t2 in
        match uu____15348 with
        | None  -> false
        | Some g ->
            let uu____15351 = discharge_guard' None env g false in
            (match uu____15351 with
             | Some uu____15355 -> true
             | None  -> false)