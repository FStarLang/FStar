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
    FStar_TypeChecker_Env.guard_t Prims.option ->
      FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun x  ->
    fun g  ->
      match g with
      | None |Some
        { FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
          FStar_TypeChecker_Env.deferred = _;
          FStar_TypeChecker_Env.univ_ineqs = _;
          FStar_TypeChecker_Env.implicits = _;_} -> g
      | Some g1 ->
          let f =
            match g1.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.NonTrivial f -> f
            | uu____62 -> failwith "impossible" in
          let uu____63 =
            let uu___136_64 = g1 in
            let uu____65 =
              let uu____66 =
                let uu____67 =
                  let uu____68 = FStar_Syntax_Syntax.mk_binder x in
                  [uu____68] in
                let uu____69 =
                  let uu____76 =
                    let uu____82 =
                      let uu____83 =
                        FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                      FStar_All.pipe_right uu____83
                        FStar_Syntax_Util.lcomp_of_comp in
                    FStar_All.pipe_right uu____82
                      (fun _0_29  -> FStar_Util.Inl _0_29) in
                  Some uu____76 in
                FStar_Syntax_Util.abs uu____67 f uu____69 in
              FStar_All.pipe_left
                (fun _0_30  -> FStar_TypeChecker_Common.NonTrivial _0_30)
                uu____66 in
            {
              FStar_TypeChecker_Env.guard_f = uu____65;
              FStar_TypeChecker_Env.deferred =
                (uu___136_64.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___136_64.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___136_64.FStar_TypeChecker_Env.implicits)
            } in
          Some uu____63
let apply_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___137_104 = g in
          let uu____105 =
            let uu____106 =
              let uu____107 =
                let uu____110 =
                  let uu____111 =
                    let uu____121 =
                      let uu____123 = FStar_Syntax_Syntax.as_arg e in
                      [uu____123] in
                    (f, uu____121) in
                  FStar_Syntax_Syntax.Tm_app uu____111 in
                FStar_Syntax_Syntax.mk uu____110 in
              uu____107
                (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun _0_31  -> FStar_TypeChecker_Common.NonTrivial _0_31)
              uu____106 in
          {
            FStar_TypeChecker_Env.guard_f = uu____105;
            FStar_TypeChecker_Env.deferred =
              (uu___137_104.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___137_104.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___137_104.FStar_TypeChecker_Env.implicits)
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
          let uu___138_145 = g in
          let uu____146 =
            let uu____147 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____147 in
          {
            FStar_TypeChecker_Env.guard_f = uu____146;
            FStar_TypeChecker_Env.deferred =
              (uu___138_145.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___138_145.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___138_145.FStar_TypeChecker_Env.implicits)
          }
let trivial: FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____151 -> failwith "impossible"
let conj_guard_f:
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g)
        |(g,FStar_TypeChecker_Common.Trivial ) -> g
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let uu____161 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____161
let check_trivial:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_TypeChecker_Common.guard_formula
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____170 -> FStar_TypeChecker_Common.NonTrivial t
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
            ((FStar_List.append
                (Prims.fst g1.FStar_TypeChecker_Env.univ_ineqs)
                (Prims.fst g2.FStar_TypeChecker_Env.univ_ineqs)),
              (FStar_List.append
                 (Prims.snd g1.FStar_TypeChecker_Env.univ_ineqs)
                 (Prims.snd g2.FStar_TypeChecker_Env.univ_ineqs)));
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
                       let uu____248 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____248
                       then f1
                       else FStar_Syntax_Util.mk_forall u (Prims.fst b) f1)
                us bs f in
            let uu___139_250 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___139_250.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___139_250.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___139_250.FStar_TypeChecker_Env.implicits)
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
               let uu____264 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____264
               then f1
               else
                 (let u =
                    env.FStar_TypeChecker_Env.universe_of env
                      (Prims.fst b).FStar_Syntax_Syntax.sort in
                  FStar_Syntax_Util.mk_forall u (Prims.fst b) f1)) bs f
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
            let uu___140_277 = g in
            let uu____278 =
              let uu____279 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____279 in
            {
              FStar_TypeChecker_Env.guard_f = uu____278;
              FStar_TypeChecker_Env.deferred =
                (uu___140_277.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___140_277.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___140_277.FStar_TypeChecker_Env.implicits)
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
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k)))
                (Some (k.FStar_Syntax_Syntax.n)) r in
            (uv1, uv1)
        | uu____324 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____339 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____339 in
            let uv1 =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k')))
                None r in
            let uu____359 =
              (FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_app (uv1, args)))
                (Some (k.FStar_Syntax_Syntax.n)) r in
            (uu____359, uv1)
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
  fun uu___108_585  ->
    match uu___108_585 with
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
    fun uu___109_665  ->
      match uu___109_665 with
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
                            (Prims.fst
                               p.FStar_TypeChecker_Common.logical_guard) in
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
    fun uu___110_703  ->
      match uu___110_703 with
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
        let uu___141_792 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___141_792.wl_deferred);
          ctr = (uu___141_792.ctr);
          defer_ok = (uu___141_792.defer_ok);
          smt_ok;
          tcenv = (uu___141_792.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___142_817 = empty_worklist env in
  let uu____818 = FStar_List.map Prims.snd g in
  {
    attempting = uu____818;
    wl_deferred = (uu___142_817.wl_deferred);
    ctr = (uu___142_817.ctr);
    defer_ok = false;
    smt_ok = (uu___142_817.smt_ok);
    tcenv = (uu___142_817.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___143_830 = wl in
        {
          attempting = (uu___143_830.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___143_830.ctr);
          defer_ok = (uu___143_830.defer_ok);
          smt_ok = (uu___143_830.smt_ok);
          tcenv = (uu___143_830.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___144_842 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___144_842.wl_deferred);
        ctr = (uu___144_842.ctr);
        defer_ok = (uu___144_842.defer_ok);
        smt_ok = (uu___144_842.smt_ok);
        tcenv = (uu___144_842.tcenv)
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
  fun uu___111_858  ->
    match uu___111_858 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___145_874 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___145_874.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___145_874.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___145_874.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___145_874.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___145_874.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___145_874.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___145_874.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___112_895  ->
    match uu___112_895 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_32  -> FStar_TypeChecker_Common.TProb _0_32)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_33  -> FStar_TypeChecker_Common.CProb _0_33)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___113_911  ->
      match uu___113_911 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___114_914  ->
    match uu___114_914 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___115_923  ->
    match uu___115_923 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___116_933  ->
    match uu___116_933 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___117_943  ->
    match uu___117_943 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun uu___118_954  ->
    match uu___118_954 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___119_965  ->
    match uu___119_965 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___120_974  ->
    match uu___120_974 with
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
         (fun uu___121_1223  ->
            match uu___121_1223 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Unionfind.union u u'
                 | uu____1230 -> FStar_Unionfind.change u (Some t))
            | TERM ((u,uu____1233),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term Prims.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___122_1256  ->
           match uu___122_1256 with
           | UNIV uu____1258 -> None
           | TERM ((u,uu____1262),t) ->
               let uu____1266 = FStar_Unionfind.equivalent uv u in
               if uu____1266 then Some t else None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe Prims.option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___123_1285  ->
           match uu___123_1285 with
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
let norm_arg env t =
  let uu____1327 = sn env (Prims.fst t) in (uu____1327, (Prims.snd t))
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
                    let uu___146_1352 = x in
                    let uu____1353 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___146_1352.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___146_1352.FStar_Syntax_Syntax.index);
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
    | FStar_Syntax_Syntax.Tm_uinst _
      |FStar_Syntax_Syntax.Tm_fvar _|FStar_Syntax_Syntax.Tm_app _ ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1553 =
             let uu____1554 = FStar_Syntax_Subst.compress t1' in
             uu____1554.FStar_Syntax_Syntax.n in
           match uu____1553 with
           | FStar_Syntax_Syntax.Tm_refine uu____1566 -> aux true t1'
           | uu____1571 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_type _
      |FStar_Syntax_Syntax.Tm_constant _
       |FStar_Syntax_Syntax.Tm_name _
        |FStar_Syntax_Syntax.Tm_bvar _
         |FStar_Syntax_Syntax.Tm_arrow _
          |FStar_Syntax_Syntax.Tm_abs _
           |FStar_Syntax_Syntax.Tm_uvar _
            |FStar_Syntax_Syntax.Tm_let _|FStar_Syntax_Syntax.Tm_match _
        -> (t11, None)
    | FStar_Syntax_Syntax.Tm_meta _
      |FStar_Syntax_Syntax.Tm_ascribed _
       |FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1606 =
          let uu____1607 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1608 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1607
            uu____1608 in
        failwith uu____1606 in
  let uu____1618 = whnf env t1 in aux false uu____1618
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1627 =
        let uu____1637 = empty_worklist env in
        base_and_refinement env uu____1637 t in
      FStar_All.pipe_right uu____1627 Prims.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____1661 = FStar_Syntax_Syntax.null_bv t in
    (uu____1661, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____1681 = base_and_refinement env wl t in
  match uu____1681 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
let force_refinement uu____1740 =
  match uu____1740 with
  | (t_base,refopt) ->
      let uu____1754 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base in
      (match uu____1754 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___124_1778  ->
      match uu___124_1778 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1782 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____1783 =
            let uu____1784 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____1784 in
          let uu____1785 =
            let uu____1786 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____1786 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____1782 uu____1783
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1785
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1790 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____1791 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____1792 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____1790 uu____1791
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1792
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____1796 =
      let uu____1798 =
        let uu____1800 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____1810  ->
                  match uu____1810 with | (uu____1814,uu____1815,x) -> x)) in
        FStar_List.append wl.attempting uu____1800 in
      FStar_List.map (wl_prob_to_string wl) uu____1798 in
    FStar_All.pipe_right uu____1796 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____1833 =
          let uu____1843 =
            let uu____1844 = FStar_Syntax_Subst.compress k in
            uu____1844.FStar_Syntax_Syntax.n in
          match uu____1843 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____1885 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____1885)
              else
                (let uu____1899 = FStar_Syntax_Util.abs_formals t in
                 match uu____1899 with
                 | (ys',t1,uu____1920) ->
                     let uu____1933 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____1933))
          | uu____1954 ->
              let uu____1955 =
                let uu____1961 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____1961) in
              ((ys, t), uu____1955) in
        match uu____1833 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2016 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2016 c in
               let uu____2018 =
                 let uu____2025 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_36  -> FStar_Util.Inl _0_36) in
                 FStar_All.pipe_right uu____2025 (fun _0_37  -> Some _0_37) in
               FStar_Syntax_Util.abs ys1 t1 uu____2018)
let solve_prob':
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term Prims.option ->
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
            let uu____2076 = p_guard prob in
            match uu____2076 with
            | (uu____2079,uv) ->
                ((let uu____2082 =
                    let uu____2083 = FStar_Syntax_Subst.compress uv in
                    uu____2083.FStar_Syntax_Syntax.n in
                  match uu____2082 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2103 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2103
                        then
                          let uu____2104 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2105 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2106 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2104
                            uu____2105 uu____2106
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2110 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___147_2113 = wl in
                  {
                    attempting = (uu___147_2113.attempting);
                    wl_deferred = (uu___147_2113.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___147_2113.defer_ok);
                    smt_ok = (uu___147_2113.smt_ok);
                    tcenv = (uu___147_2113.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2126 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2126
         then
           let uu____2127 = FStar_Util.string_of_int pid in
           let uu____2128 =
             let uu____2129 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2129 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2127 uu____2128
         else ());
        commit sol;
        (let uu___148_2134 = wl in
         {
           attempting = (uu___148_2134.attempting);
           wl_deferred = (uu___148_2134.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___148_2134.defer_ok);
           smt_ok = (uu___148_2134.smt_ok);
           tcenv = (uu___148_2134.tcenv)
         })
let solve_prob:
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term Prims.option ->
      uvi Prims.list -> worklist -> worklist
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          let conj_guard1 t g =
            match (t, g) with
            | (uu____2163,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2171 = FStar_Syntax_Util.mk_conj t1 f in
                Some uu____2171 in
          (let uu____2177 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2177
           then
             let uu____2178 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2179 =
               let uu____2180 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2180 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2178 uu____2179
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2205 =
    let uu____2209 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2209 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2205
    (FStar_Util.for_some
       (fun uu____2230  ->
          match uu____2230 with
          | (uv,uu____2238) -> FStar_Unionfind.equivalent uv (Prims.fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2282 = occurs wl uk t in Prims.op_Negation uu____2282 in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2287 =
         let uu____2288 = FStar_Syntax_Print.uvar_to_string (Prims.fst uk) in
         let uu____2292 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2288 uu____2292 in
       Some uu____2287) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2340 = occurs_check env wl uk t in
  match uu____2340 with
  | (occurs_ok,msg) ->
      let uu____2357 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2357, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (Prims.fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2421 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2445  ->
            fun uu____2446  ->
              match (uu____2445, uu____2446) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2489 =
                    let uu____2490 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2490 in
                  if uu____2489
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2504 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2504
                     then
                       let uu____2511 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____2511)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2421 with | (isect,uu____2533) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2582  ->
          fun uu____2583  ->
            match (uu____2582, uu____2583) with
            | ((a,uu____2593),(b,uu____2595)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (Prims.fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2639 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2645  ->
                match uu____2645 with
                | (b,uu____2649) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____2639 then None else Some (a, (Prims.snd hd1))
  | uu____2658 -> None
let rec pat_vars:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_Syntax_Syntax.binders Prims.option
  =
  fun env  ->
    fun seen  ->
      fun args  ->
        match args with
        | [] -> Some (FStar_List.rev seen)
        | hd1::rest ->
            let uu____2701 = pat_var_opt env seen hd1 in
            (match uu____2701 with
             | None  ->
                 ((let uu____2709 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____2709
                   then
                     let uu____2710 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (Prims.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____2710
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2722 =
      let uu____2723 = FStar_Syntax_Subst.compress t in
      uu____2723.FStar_Syntax_Syntax.n in
    match uu____2722 with
    | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
         FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
         FStar_Syntax_Syntax.vars = _;_},_)
        -> true
    | uu____2739 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____2801;
         FStar_Syntax_Syntax.pos = uu____2802;
         FStar_Syntax_Syntax.vars = uu____2803;_},args)
      -> (t, uv, k, args)
  | uu____2844 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____2898 = destruct_flex_t t in
  match uu____2898 with
  | (t1,uv,k,args) ->
      let uu____2966 = pat_vars env [] args in
      (match uu____2966 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3022 -> ((t1, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth Prims.option*
  FStar_Syntax_Syntax.delta_depth Prims.option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3070 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth Prims.option*
      FStar_Syntax_Syntax.delta_depth Prims.option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3093 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3097 -> false
let head_match: match_result -> match_result =
  fun uu___125_3100  ->
    match uu___125_3100 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3109 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3122 ->
          let uu____3123 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3123 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3133 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth Prims.option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta _|FStar_Syntax_Syntax.Tm_delayed _ ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown 
        |FStar_Syntax_Syntax.Tm_bvar _
         |FStar_Syntax_Syntax.Tm_name _
          |FStar_Syntax_Syntax.Tm_uvar _
           |FStar_Syntax_Syntax.Tm_let _|FStar_Syntax_Syntax.Tm_match _
          -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,_)
        |FStar_Syntax_Syntax.Tm_ascribed (t2,_,_)
         |FStar_Syntax_Syntax.Tm_app (t2,_)|FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
             FStar_Syntax_Syntax.sort = t2;_},_)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant _
        |FStar_Syntax_Syntax.Tm_type _
         |FStar_Syntax_Syntax.Tm_arrow _|FStar_Syntax_Syntax.Tm_abs _ ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3201 = fv_delta_depth env fv in Some uu____3201
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
            let uu____3220 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3220
            then FullMatch
            else
              (let uu____3222 =
                 let uu____3227 =
                   let uu____3229 = fv_delta_depth env f in Some uu____3229 in
                 let uu____3230 =
                   let uu____3232 = fv_delta_depth env g in Some uu____3232 in
                 (uu____3227, uu____3230) in
               MisMatch uu____3222)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3236),FStar_Syntax_Syntax.Tm_uinst (g,uu____3238)) ->
            let uu____3247 = head_matches env f g in
            FStar_All.pipe_right uu____3247 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3254),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3256)) ->
            let uu____3281 = FStar_Unionfind.equivalent uv uv' in
            if uu____3281 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3289),FStar_Syntax_Syntax.Tm_refine (y,uu____3291)) ->
            let uu____3300 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3300 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3302),uu____3303) ->
            let uu____3308 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3308 head_match
        | (uu____3309,FStar_Syntax_Syntax.Tm_refine (x,uu____3311)) ->
            let uu____3316 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3316 head_match
        | (FStar_Syntax_Syntax.Tm_type _,FStar_Syntax_Syntax.Tm_type _)
          |(FStar_Syntax_Syntax.Tm_arrow _,FStar_Syntax_Syntax.Tm_arrow _) ->
            HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3322),FStar_Syntax_Syntax.Tm_app (head',uu____3324))
            ->
            let uu____3353 = head_matches env head1 head' in
            FStar_All.pipe_right uu____3353 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3355),uu____3356) ->
            let uu____3371 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____3371 head_match
        | (uu____3372,FStar_Syntax_Syntax.Tm_app (head1,uu____3374)) ->
            let uu____3389 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____3389 head_match
        | uu____3390 ->
            let uu____3393 =
              let uu____3398 = delta_depth_of_term env t11 in
              let uu____3400 = delta_depth_of_term env t21 in
              (uu____3398, uu____3400) in
            MisMatch uu____3393
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3436 = FStar_Syntax_Util.head_and_args t in
    match uu____3436 with
    | (head1,uu____3448) ->
        let uu____3463 =
          let uu____3464 = FStar_Syntax_Util.un_uinst head1 in
          uu____3464.FStar_Syntax_Syntax.n in
        (match uu____3463 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3469 =
               let uu____3470 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____3470 FStar_Option.isSome in
             if uu____3469
             then
               let uu____3484 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____3484 (fun _0_38  -> Some _0_38)
             else None
         | uu____3487 -> None) in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None)) in
  let fail r = (r, None) in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21 in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),_)|MisMatch
      (_,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____3567 =
             let uu____3572 = maybe_inline t11 in
             let uu____3574 = maybe_inline t21 in (uu____3572, uu____3574) in
           match uu____3567 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____3599 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____3599 with
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
        let uu____3614 =
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
             let uu____3622 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____3622)) in
        (match uu____3614 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____3630 -> fail r
    | uu____3635 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____3660 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____3690 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____3705 = FStar_Syntax_Util.type_u () in
      match uu____3705 with
      | (t,uu____3709) ->
          let uu____3710 = new_uvar r binders t in Prims.fst uu____3710
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____3719 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____3719 Prims.fst
let rec decompose:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      ((tc Prims.list -> FStar_Syntax_Syntax.term)*
        (FStar_Syntax_Syntax.term -> Prims.bool)* (FStar_Syntax_Syntax.binder
        Prims.option* variance* tc) Prims.list)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let matches t' =
        let uu____3761 = head_matches env t1 t' in
        match uu____3761 with
        | MisMatch uu____3762 -> false
        | uu____3767 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____3827,imp),T (t2,uu____3830)) -> (t2, imp)
                     | uu____3847 -> failwith "Bad reconstruction") args
                args' in
            (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1)))
              None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____3891  ->
                    match uu____3891 with
                    | (t2,uu____3899) ->
                        (None, INVARIANT, (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let fail uu____3932 = failwith "Bad reconstruction" in
          let uu____3933 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____3933 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____3986))::tcs2) ->
                       aux
                         (((let uu___149_4008 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___149_4008.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___149_4008.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4018 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___126_4049 =
                 match uu___126_4049 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((Prims.fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4112 = decompose1 [] bs1 in
               (rebuild, matches, uu____4112))
      | uu____4140 ->
          let rebuild uu___127_4145 =
            match uu___127_4145 with
            | [] -> t1
            | uu____4147 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___128_4166  ->
    match uu___128_4166 with
    | T (t,uu____4168) -> t
    | uu____4177 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___129_4180  ->
    match uu___129_4180 with
    | T (t,uu____4182) -> FStar_Syntax_Syntax.as_arg t
    | uu____4191 -> failwith "Impossible"
let imitation_sub_probs:
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.args ->
          (FStar_Syntax_Syntax.binder Prims.option* variance* tc) Prims.list
            ->
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
              | (uu____4260,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4279 = new_uvar r scope1 k in
                  (match uu____4279 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4291 ->
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_app (gi, args))) None
                               r in
                       let uu____4310 =
                         let uu____4311 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_39  ->
                              FStar_TypeChecker_Common.TProb _0_39)
                           uu____4311 in
                       ((T (gi_xs, mk_kind)), uu____4310))
              | (uu____4320,uu____4321,C uu____4322) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4409 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4420;
                         FStar_Syntax_Syntax.pos = uu____4421;
                         FStar_Syntax_Syntax.vars = uu____4422;_})
                        ->
                        let uu____4437 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4437 with
                         | (T (gi_xs,uu____4453),prob) ->
                             let uu____4463 =
                               let uu____4464 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_40  -> C _0_40)
                                 uu____4464 in
                             (uu____4463, [prob])
                         | uu____4466 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4476;
                         FStar_Syntax_Syntax.pos = uu____4477;
                         FStar_Syntax_Syntax.vars = uu____4478;_})
                        ->
                        let uu____4493 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4493 with
                         | (T (gi_xs,uu____4509),prob) ->
                             let uu____4519 =
                               let uu____4520 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_41  -> C _0_41)
                                 uu____4520 in
                             (uu____4519, [prob])
                         | uu____4522 -> failwith "impossible")
                    | (uu____4528,uu____4529,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____4531;
                         FStar_Syntax_Syntax.pos = uu____4532;
                         FStar_Syntax_Syntax.vars = uu____4533;_})
                        ->
                        let components =
                          FStar_All.pipe_right
                            c.FStar_Syntax_Syntax.effect_args
                            (FStar_List.map
                               (fun t  ->
                                  (None, INVARIANT,
                                    (T ((Prims.fst t), generic_kind))))) in
                        let components1 =
                          (None, COVARIANT,
                            (T
                               ((c.FStar_Syntax_Syntax.result_typ),
                                 kind_type)))
                          :: components in
                        let uu____4607 =
                          let uu____4612 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____4612 FStar_List.unzip in
                        (match uu____4607 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____4641 =
                                 let uu____4642 =
                                   let uu____4645 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____4645 un_T in
                                 let uu____4646 =
                                   let uu____4652 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____4652
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____4642;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____4646;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____4641 in
                             ((C gi_xs), sub_probs))
                    | uu____4657 ->
                        let uu____4664 = sub_prob scope1 args q in
                        (match uu____4664 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____4409 with
                   | (tc,probs) ->
                       let uu____4682 =
                         match q with
                         | (Some b,uu____4708,uu____4709) ->
                             let uu____4717 =
                               let uu____4721 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____4721 :: args in
                             ((Some b), (b :: scope1), uu____4717)
                         | uu____4739 -> (None, scope1, args) in
                       (match uu____4682 with
                        | (bopt,scope2,args1) ->
                            let uu____4782 = aux scope2 args1 qs2 in
                            (match uu____4782 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____4803 =
                                         let uu____4805 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob) Prims.fst)) in
                                         f :: uu____4805 in
                                       FStar_Syntax_Util.mk_conj_l uu____4803
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (Prims.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____4818 =
                                         let uu____4820 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (Prims.fst b) f in
                                         let uu____4821 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob) Prims.fst)) in
                                         uu____4820 :: uu____4821 in
                                       FStar_Syntax_Util.mk_conj_l uu____4818 in
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
    Prims.option* variance* tc) Prims.list))
let rigid_rigid: Prims.int = Prims.parse_int "0"
let flex_rigid_eq: Prims.int = Prims.parse_int "1"
let flex_refine_inner: Prims.int = Prims.parse_int "2"
let flex_refine: Prims.int = Prims.parse_int "3"
let flex_rigid: Prims.int = Prims.parse_int "4"
let rigid_flex: Prims.int = Prims.parse_int "5"
let refine_flex: Prims.int = Prims.parse_int "6"
let flex_flex: Prims.int = Prims.parse_int "7"
let compress_tprob wl p =
  let uu___150_4874 = p in
  let uu____4877 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____4878 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___150_4874.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____4877;
    FStar_TypeChecker_Common.relation =
      (uu___150_4874.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____4878;
    FStar_TypeChecker_Common.element =
      (uu___150_4874.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___150_4874.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___150_4874.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___150_4874.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___150_4874.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___150_4874.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____4888 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____4888
            (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
      | FStar_TypeChecker_Common.CProb uu____4893 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____4907 = compress_prob wl pr in
        FStar_All.pipe_right uu____4907 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____4913 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____4913 with
           | (lh,uu____4926) ->
               let uu____4941 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____4941 with
                | (rh,uu____4954) ->
                    let uu____4969 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____4978,FStar_Syntax_Syntax.Tm_uvar uu____4979)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar _,_)
                        |(_,FStar_Syntax_Syntax.Tm_uvar _) when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5004,uu____5005)
                          ->
                          let uu____5014 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5014 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5054 ->
                                    let rank =
                                      let uu____5061 = is_top_level_prob prob in
                                      if uu____5061
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5063 =
                                      let uu___151_5066 = tp in
                                      let uu____5069 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___151_5066.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___151_5066.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___151_5066.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5069;
                                        FStar_TypeChecker_Common.element =
                                          (uu___151_5066.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___151_5066.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___151_5066.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___151_5066.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___151_5066.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___151_5066.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5063)))
                      | (uu____5079,FStar_Syntax_Syntax.Tm_uvar uu____5080)
                          ->
                          let uu____5089 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5089 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5129 ->
                                    let uu____5135 =
                                      let uu___152_5140 = tp in
                                      let uu____5143 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___152_5140.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5143;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___152_5140.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___152_5140.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___152_5140.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___152_5140.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___152_5140.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___152_5140.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___152_5140.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___152_5140.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5135)))
                      | (uu____5159,uu____5160) -> (rigid_rigid, tp) in
                    (match uu____4969 with
                     | (rank,tp1) ->
                         let uu____5171 =
                           FStar_All.pipe_right
                             (let uu___153_5174 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___153_5174.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___153_5174.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___153_5174.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___153_5174.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___153_5174.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___153_5174.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___153_5174.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___153_5174.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___153_5174.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_43  ->
                                FStar_TypeChecker_Common.TProb _0_43) in
                         (rank, uu____5171))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5180 =
            FStar_All.pipe_right
              (let uu___154_5183 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___154_5183.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___154_5183.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___154_5183.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___154_5183.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___154_5183.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___154_5183.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___154_5183.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___154_5183.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___154_5183.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) in
          (rigid_rigid, uu____5180)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob Prims.option*
      FStar_TypeChecker_Common.prob Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____5215 probs =
      match uu____5215 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5245 = rank wl hd1 in
               (match uu____5245 with
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
    match projectee with | UDeferred _0 -> true | uu____5310 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5322 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5334 -> false
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
                        let uu____5371 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____5371 with
                        | (k,uu____5375) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Unionfind.equivalent v1 v2
                             | uu____5380 -> false)))
            | uu____5381 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____5424 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____5424 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5427 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____5433 =
                     let uu____5434 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____5435 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5434
                       uu____5435 in
                   UFailed uu____5433)
            | (FStar_Syntax_Syntax.U_max us,u')
              |(u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5452 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5452 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____5455 ->
                let uu____5458 =
                  let uu____5459 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____5460 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5459
                    uu____5460 msg in
                UFailed uu____5458 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar _,_)
            |(FStar_Syntax_Syntax.U_unknown ,_)
             |(_,FStar_Syntax_Syntax.U_bvar _)
              |(_,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____5467 =
                let uu____5468 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5469 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5468 uu____5469 in
              failwith uu____5467
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____5481 = FStar_Unionfind.equivalent v1 v2 in
              if uu____5481
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u)
            |(u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____5494 = occurs_univ v1 u3 in
              if uu____5494
              then
                let uu____5495 =
                  let uu____5496 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____5497 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5496 uu____5497 in
                try_umax_components u11 u21 uu____5495
              else
                (let uu____5499 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____5499)
          | (FStar_Syntax_Syntax.U_max _,_)|(_,FStar_Syntax_Syntax.U_max _)
              ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____5509 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____5509
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ _,FStar_Syntax_Syntax.U_zero )
            |(FStar_Syntax_Syntax.U_succ _,FStar_Syntax_Syntax.U_name _)
             |(FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ _)
              |(FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name _)
               |(FStar_Syntax_Syntax.U_name _,FStar_Syntax_Syntax.U_succ _)
                |(FStar_Syntax_Syntax.U_name _,FStar_Syntax_Syntax.U_zero )
              -> UFailed "Incompatible universes"
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
  let uu____5580 = bc1 in
  match uu____5580 with
  | (bs1,mk_cod1) ->
      let uu____5605 = bc2 in
      (match uu____5605 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____5652 = FStar_Util.first_N n1 bs in
             match uu____5652 with
             | (bs3,rest) ->
                 let uu____5666 = mk_cod rest in (bs3, uu____5666) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____5684 =
               let uu____5688 = mk_cod1 [] in (bs1, uu____5688) in
             let uu____5690 =
               let uu____5694 = mk_cod2 [] in (bs2, uu____5694) in
             (uu____5684, uu____5690)
           else
             if l1 > l2
             then
               (let uu____5716 = curry l2 bs1 mk_cod1 in
                let uu____5723 =
                  let uu____5727 = mk_cod2 [] in (bs2, uu____5727) in
                (uu____5716, uu____5723))
             else
               (let uu____5736 =
                  let uu____5740 = mk_cod1 [] in (bs1, uu____5740) in
                let uu____5742 = curry l1 bs2 mk_cod2 in
                (uu____5736, uu____5742)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____5846 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____5846
       then
         let uu____5847 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____5847
       else ());
      (let uu____5849 = next_prob probs in
       match uu____5849 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___155_5862 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___155_5862.wl_deferred);
               ctr = (uu___155_5862.ctr);
               defer_ok = (uu___155_5862.defer_ok);
               smt_ok = (uu___155_5862.smt_ok);
               tcenv = (uu___155_5862.tcenv)
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
                  let uu____5869 = solve_flex_rigid_join env tp probs1 in
                  (match uu____5869 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____5873 = solve_rigid_flex_meet env tp probs1 in
                     match uu____5873 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____5877,uu____5878) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____5887 ->
                let uu____5892 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____5920  ->
                          match uu____5920 with
                          | (c,uu____5925,uu____5926) -> c < probs.ctr)) in
                (match uu____5892 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____5948 =
                            FStar_List.map
                              (fun uu____5954  ->
                                 match uu____5954 with
                                 | (uu____5960,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____5948
                      | uu____5963 ->
                          let uu____5968 =
                            let uu___156_5969 = probs in
                            let uu____5970 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____5979  ->
                                      match uu____5979 with
                                      | (uu____5983,uu____5984,y) -> y)) in
                            {
                              attempting = uu____5970;
                              wl_deferred = rest;
                              ctr = (uu___156_5969.ctr);
                              defer_ok = (uu___156_5969.defer_ok);
                              smt_ok = (uu___156_5969.smt_ok);
                              tcenv = (uu___156_5969.tcenv)
                            } in
                          solve env uu____5968))))
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
            let uu____5991 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____5991 with
            | USolved wl1 ->
                let uu____5993 = solve_prob orig None [] wl1 in
                solve env uu____5993
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
                  let uu____6027 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6027 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6030 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6038;
                  FStar_Syntax_Syntax.pos = uu____6039;
                  FStar_Syntax_Syntax.vars = uu____6040;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6043;
                  FStar_Syntax_Syntax.pos = uu____6044;
                  FStar_Syntax_Syntax.vars = uu____6045;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst _,_)
              |(_,FStar_Syntax_Syntax.Tm_uinst _) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6061 -> USolved wl
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
            ((let uu____6069 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6069
              then
                let uu____6070 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6070 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist Prims.option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6078 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6078
         then
           let uu____6079 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6079
         else ());
        (let uu____6081 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6081 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6123 = head_matches_delta env () t1 t2 in
               match uu____6123 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6145 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6171 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6180 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____6181 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____6180, uu____6181)
                          | None  ->
                              let uu____6184 = FStar_Syntax_Subst.compress t1 in
                              let uu____6185 = FStar_Syntax_Subst.compress t2 in
                              (uu____6184, uu____6185) in
                        (match uu____6171 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6207 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_45  ->
                                    FStar_TypeChecker_Common.TProb _0_45)
                                 uu____6207 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6230 =
                                    let uu____6236 =
                                      let uu____6239 =
                                        let uu____6242 =
                                          let uu____6243 =
                                            let uu____6248 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____6248) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6243 in
                                        FStar_Syntax_Syntax.mk uu____6242 in
                                      uu____6239 None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____6261 =
                                      let uu____6263 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____6263] in
                                    (uu____6236, uu____6261) in
                                  Some uu____6230
                              | (uu____6272,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6274)) ->
                                  let uu____6279 =
                                    let uu____6283 =
                                      let uu____6285 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____6285] in
                                    (t11, uu____6283) in
                                  Some uu____6279
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6291),uu____6292) ->
                                  let uu____6297 =
                                    let uu____6301 =
                                      let uu____6303 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____6303] in
                                    (t21, uu____6301) in
                                  Some uu____6297
                              | uu____6308 ->
                                  let uu____6311 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____6311 with
                                   | (head1,uu____6326) ->
                                       let uu____6341 =
                                         let uu____6342 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____6342.FStar_Syntax_Syntax.n in
                                       (match uu____6341 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6349;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6351;_}
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
                                        | uu____6360 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6369) ->
                  let uu____6382 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___130_6391  ->
                            match uu___130_6391 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6396 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____6396 with
                                      | (u',uu____6407) ->
                                          let uu____6422 =
                                            let uu____6423 = whnf env u' in
                                            uu____6423.FStar_Syntax_Syntax.n in
                                          (match uu____6422 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____6427) ->
                                               FStar_Unionfind.equivalent uv
                                                 uv'
                                           | uu____6443 -> false))
                                 | uu____6444 -> false)
                            | uu____6446 -> false)) in
                  (match uu____6382 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____6467 tps =
                         match uu____6467 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____6494 =
                                    let uu____6499 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____6499 in
                                  (match uu____6494 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____6518 -> None) in
                       let uu____6523 =
                         let uu____6528 =
                           let uu____6532 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____6532, []) in
                         make_lower_bound uu____6528 lower_bounds in
                       (match uu____6523 with
                        | None  ->
                            ((let uu____6539 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____6539
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
                            ((let uu____6552 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____6552
                              then
                                let wl' =
                                  let uu___157_6554 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___157_6554.wl_deferred);
                                    ctr = (uu___157_6554.ctr);
                                    defer_ok = (uu___157_6554.defer_ok);
                                    smt_ok = (uu___157_6554.smt_ok);
                                    tcenv = (uu___157_6554.tcenv)
                                  } in
                                let uu____6555 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____6555
                              else ());
                             (let uu____6557 =
                                solve_t env eq_prob
                                  (let uu___158_6558 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___158_6558.wl_deferred);
                                     ctr = (uu___158_6558.ctr);
                                     defer_ok = (uu___158_6558.defer_ok);
                                     smt_ok = (uu___158_6558.smt_ok);
                                     tcenv = (uu___158_6558.tcenv)
                                   }) in
                              match uu____6557 with
                              | Success uu____6560 ->
                                  let wl1 =
                                    let uu___159_6562 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___159_6562.wl_deferred);
                                      ctr = (uu___159_6562.ctr);
                                      defer_ok = (uu___159_6562.defer_ok);
                                      smt_ok = (uu___159_6562.smt_ok);
                                      tcenv = (uu___159_6562.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1 in
                                  let uu____6564 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds in
                                  Some wl2
                              | uu____6567 -> None))))
              | uu____6568 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist Prims.option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6575 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6575
         then
           let uu____6576 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____6576
         else ());
        (let uu____6578 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____6578 with
         | (u,args) ->
             let uu____6605 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____6605 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____6636 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____6636 with
                    | (h1,args1) ->
                        let uu____6664 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____6664 with
                         | (h2,uu____6677) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____6696 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____6696
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____6709 =
                                          let uu____6711 =
                                            let uu____6712 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_46  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_46) uu____6712 in
                                          [uu____6711] in
                                        Some uu____6709))
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
                                       (let uu____6734 =
                                          let uu____6736 =
                                            let uu____6737 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_47  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_47) uu____6737 in
                                          [uu____6736] in
                                        Some uu____6734))
                                  else None
                              | uu____6745 -> None)) in
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
                             let uu____6811 =
                               let uu____6817 =
                                 let uu____6820 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____6820 in
                               (uu____6817, m1) in
                             Some uu____6811)
                    | (uu____6829,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____6831)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____6863),uu____6864) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____6895 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6929) ->
                       let uu____6942 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___131_6951  ->
                                 match uu___131_6951 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____6956 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____6956 with
                                           | (u',uu____6967) ->
                                               let uu____6982 =
                                                 let uu____6983 = whnf env u' in
                                                 uu____6983.FStar_Syntax_Syntax.n in
                                               (match uu____6982 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____6987) ->
                                                    FStar_Unionfind.equivalent
                                                      uv uv'
                                                | uu____7003 -> false))
                                      | uu____7004 -> false)
                                 | uu____7006 -> false)) in
                       (match uu____6942 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7031 tps =
                              match uu____7031 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7072 =
                                         let uu____7079 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7079 in
                                       (match uu____7072 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7114 -> None) in
                            let uu____7121 =
                              let uu____7128 =
                                let uu____7134 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7134, []) in
                              make_upper_bound uu____7128 upper_bounds in
                            (match uu____7121 with
                             | None  ->
                                 ((let uu____7143 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7143
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
                                 ((let uu____7162 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7162
                                   then
                                     let wl' =
                                       let uu___160_7164 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___160_7164.wl_deferred);
                                         ctr = (uu___160_7164.ctr);
                                         defer_ok = (uu___160_7164.defer_ok);
                                         smt_ok = (uu___160_7164.smt_ok);
                                         tcenv = (uu___160_7164.tcenv)
                                       } in
                                     let uu____7165 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7165
                                   else ());
                                  (let uu____7167 =
                                     solve_t env eq_prob
                                       (let uu___161_7168 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___161_7168.wl_deferred);
                                          ctr = (uu___161_7168.ctr);
                                          defer_ok = (uu___161_7168.defer_ok);
                                          smt_ok = (uu___161_7168.smt_ok);
                                          tcenv = (uu___161_7168.tcenv)
                                        }) in
                                   match uu____7167 with
                                   | Success uu____7170 ->
                                       let wl1 =
                                         let uu___162_7172 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___162_7172.wl_deferred);
                                           ctr = (uu___162_7172.ctr);
                                           defer_ok =
                                             (uu___162_7172.defer_ok);
                                           smt_ok = (uu___162_7172.smt_ok);
                                           tcenv = (uu___162_7172.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1 in
                                       let uu____7174 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds in
                                       Some wl2
                                   | uu____7177 -> None))))
                   | uu____7178 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____7243 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____7243
                      then
                        let uu____7244 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7244
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob) Prims.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___163_7276 = hd1 in
                      let uu____7277 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___163_7276.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___163_7276.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7277
                      } in
                    let hd21 =
                      let uu___164_7281 = hd2 in
                      let uu____7282 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___164_7281.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___164_7281.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7282
                      } in
                    let prob =
                      let uu____7286 =
                        let uu____7289 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7289 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_48  -> FStar_TypeChecker_Common.TProb _0_48)
                        uu____7286 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____7297 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7297 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____7300 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____7300 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7318 =
                             FStar_All.pipe_right (p_guard prob) Prims.fst in
                           let uu____7321 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____7318 uu____7321 in
                         ((let uu____7327 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____7327
                           then
                             let uu____7328 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____7329 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7328 uu____7329
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7344 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____7350 = aux scope env [] bs1 bs2 in
              match uu____7350 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7366 = compress_tprob wl problem in
        solve_t' env uu____7366 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7399 = head_matches_delta env1 wl1 t1 t2 in
          match uu____7399 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7416,uu____7417) ->
                   let may_relate head3 =
                     let uu____7432 =
                       let uu____7433 = FStar_Syntax_Util.un_uinst head3 in
                       uu____7433.FStar_Syntax_Syntax.n in
                     match uu____7432 with
                     | FStar_Syntax_Syntax.Tm_name _
                       |FStar_Syntax_Syntax.Tm_match _ -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____7439 -> false in
                   let uu____7440 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____7440
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
                                let uu____7457 =
                                  let uu____7458 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____7458 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____7457 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____7460 = solve_prob orig (Some guard) [] wl1 in
                     solve env1 uu____7460
                   else giveup env1 "head mismatch" orig
               | (uu____7462,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___165_7470 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___165_7470.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___165_7470.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___165_7470.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___165_7470.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___165_7470.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___165_7470.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___165_7470.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___165_7470.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____7471,None ) ->
                   ((let uu____7478 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____7478
                     then
                       let uu____7479 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____7480 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____7481 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____7482 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____7479
                         uu____7480 uu____7481 uu____7482
                     else ());
                    (let uu____7484 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____7484 with
                     | (head11,args1) ->
                         let uu____7510 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____7510 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____7550 =
                                  let uu____7551 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____7552 = args_to_string args1 in
                                  let uu____7553 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____7554 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____7551 uu____7552 uu____7553
                                    uu____7554 in
                                giveup env1 uu____7550 orig
                              else
                                (let uu____7556 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____7559 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____7559 = FStar_Syntax_Util.Equal) in
                                 if uu____7556
                                 then
                                   let uu____7560 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____7560 with
                                   | USolved wl2 ->
                                       let uu____7562 =
                                         solve_prob orig None [] wl2 in
                                       solve env1 uu____7562
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____7566 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____7566 with
                                    | (base1,refinement1) ->
                                        let uu____7592 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____7592 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____7646 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____7646 with
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
                                                           (fun uu____7656 
                                                              ->
                                                              fun uu____7657 
                                                                ->
                                                                match 
                                                                  (uu____7656,
                                                                    uu____7657)
                                                                with
                                                                | ((a,uu____7667),
                                                                   (a',uu____7669))
                                                                    ->
                                                                    let uu____7674
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
                                                                    uu____7674)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____7680 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                Prims.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____7680 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____7684 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___166_7717 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___166_7717.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___166_7717.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___166_7717.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___166_7717.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___166_7717.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___166_7717.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___166_7717.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___166_7717.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____7737 = p in
          match uu____7737 with
          | (((u,k),xs,c),ps,(h,uu____7748,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____7797 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____7797 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____7811 = h gs_xs in
                     let uu____7812 =
                       let uu____7819 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_50  -> FStar_Util.Inl _0_50) in
                       FStar_All.pipe_right uu____7819
                         (fun _0_51  -> Some _0_51) in
                     FStar_Syntax_Util.abs xs1 uu____7811 uu____7812 in
                   ((let uu____7850 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____7850
                     then
                       let uu____7851 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____7852 = FStar_Syntax_Print.comp_to_string c in
                       let uu____7853 = FStar_Syntax_Print.term_to_string im in
                       let uu____7854 = FStar_Syntax_Print.tag_of_term im in
                       let uu____7855 =
                         let uu____7856 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____7856
                           (FStar_String.concat ", ") in
                       let uu____7859 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____7851 uu____7852 uu____7853 uu____7854
                         uu____7855 uu____7859
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___132_7877 =
          match uu___132_7877 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____7906 = p in
          match uu____7906 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____7964 = FStar_List.nth ps i in
              (match uu____7964 with
               | (pi,uu____7967) ->
                   let uu____7972 = FStar_List.nth xs i in
                   (match uu____7972 with
                    | (xi,uu____7979) ->
                        let rec gs k =
                          let uu____7988 = FStar_Syntax_Util.arrow_formals k in
                          match uu____7988 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8040)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8048 = new_uvar r xs k_a in
                                    (match uu____8048 with
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
                                         let uu____8067 = aux subst2 tl1 in
                                         (match uu____8067 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8082 =
                                                let uu____8084 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8084 :: gi_xs' in
                                              let uu____8085 =
                                                let uu____8087 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8087 :: gi_ps' in
                                              (uu____8082, uu____8085))) in
                              aux [] bs in
                        let uu____8090 =
                          let uu____8091 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8091 in
                        if uu____8090
                        then None
                        else
                          (let uu____8094 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8094 with
                           | (g_xs,uu____8101) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8108 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r in
                                 let uu____8113 =
                                   let uu____8120 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_52  -> FStar_Util.Inl _0_52) in
                                   FStar_All.pipe_right uu____8120
                                     (fun _0_53  -> Some _0_53) in
                                 FStar_Syntax_Util.abs xs uu____8108
                                   uu____8113 in
                               let sub1 =
                                 let uu____8151 =
                                   let uu____8154 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let uu____8161 =
                                     let uu____8164 =
                                       FStar_List.map
                                         (fun uu____8170  ->
                                            match uu____8170 with
                                            | (uu____8175,uu____8176,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____8164 in
                                   mk_problem (p_scope orig) orig uu____8154
                                     (p_rel orig) uu____8161 None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_54  ->
                                      FStar_TypeChecker_Common.TProb _0_54)
                                   uu____8151 in
                               ((let uu____8186 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____8186
                                 then
                                   let uu____8187 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____8188 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8187 uu____8188
                                 else ());
                                (let wl2 =
                                   let uu____8191 =
                                     let uu____8193 =
                                       FStar_All.pipe_left Prims.fst
                                         (p_guard sub1) in
                                     Some uu____8193 in
                                   solve_prob orig uu____8191
                                     [TERM (u, proj)] wl1 in
                                 let uu____8198 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_55  -> Some _0_55) uu____8198))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8222 = lhs in
          match uu____8222 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8245 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____8245 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8267 =
                        let uu____8293 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____8293) in
                      Some uu____8267
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____8376 =
                           let uu____8380 =
                             let uu____8381 = FStar_Syntax_Subst.compress k in
                             uu____8381.FStar_Syntax_Syntax.n in
                           (uu____8380, args) in
                         match uu____8376 with
                         | (uu____8388,[]) ->
                             let uu____8390 =
                               let uu____8396 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____8396) in
                             Some uu____8390
                         | (FStar_Syntax_Syntax.Tm_uvar _,_)
                           |(FStar_Syntax_Syntax.Tm_app _,_) ->
                             let uu____8413 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____8413 with
                              | (uv1,uv_args) ->
                                  let uu____8442 =
                                    let uu____8443 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____8443.FStar_Syntax_Syntax.n in
                                  (match uu____8442 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____8450) ->
                                       let uu____8463 =
                                         pat_vars env [] uv_args in
                                       (match uu____8463 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____8477  ->
                                                      let uu____8478 =
                                                        let uu____8479 =
                                                          let uu____8480 =
                                                            let uu____8483 =
                                                              let uu____8484
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____8484
                                                                Prims.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____8483 in
                                                          Prims.fst
                                                            uu____8480 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____8479 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____8478)) in
                                            let c1 =
                                              let uu____8490 =
                                                let uu____8491 =
                                                  let uu____8494 =
                                                    let uu____8495 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____8495 Prims.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____8494 in
                                                Prims.fst uu____8491 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____8490 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____8504 =
                                                let uu____8511 =
                                                  let uu____8517 =
                                                    let uu____8518 =
                                                      let uu____8521 =
                                                        let uu____8522 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____8522
                                                          Prims.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____8521 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____8518 in
                                                  FStar_Util.Inl uu____8517 in
                                                Some uu____8511 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____8504 in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             Some (xs1, c1)))
                                   | uu____8545 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____8550)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____8576 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____8576
                                 (fun _0_56  -> Some _0_56)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____8595 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____8595 with
                                  | (args1,rest) ->
                                      let uu____8611 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____8611 with
                                       | (xs2,c2) ->
                                           let uu____8619 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____8619
                                             (fun uu____8630  ->
                                                match uu____8630 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____8652 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____8652 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____8698 =
                                        let uu____8701 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____8701 in
                                      FStar_All.pipe_right uu____8698
                                        (fun _0_57  -> Some _0_57))
                         | uu____8709 ->
                             let uu____8713 =
                               let uu____8714 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____8718 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____8719 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____8714 uu____8718 uu____8719 in
                             failwith uu____8713 in
                       let uu____8723 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____8723
                         (fun uu____8751  ->
                            match uu____8751 with
                            | (xs1,c1) ->
                                let uu____8779 =
                                  let uu____8802 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____8802) in
                                Some uu____8779)) in
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
                     let uu____8874 = imitate orig env wl1 st in
                     match uu____8874 with
                     | Failed uu____8879 ->
                         (FStar_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____8885 = project orig env wl1 i st in
                      match uu____8885 with
                      | None |Some (Failed _) ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____8903 = FStar_Syntax_Util.head_and_args t21 in
                match uu____8903 with
                | (hd1,uu____8914) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow _
                       |FStar_Syntax_Syntax.Tm_constant _
                        |FStar_Syntax_Syntax.Tm_abs _ -> true
                     | uu____8932 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____8935 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____8935
                         then true
                         else
                           ((let uu____8938 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____8938
                             then
                               let uu____8939 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____8939
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____8947 =
                    let uu____8950 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____8950 Prims.fst in
                  FStar_All.pipe_right uu____8947 FStar_Syntax_Free.names in
                let uu____8981 = FStar_Util.set_is_empty fvs_hd in
                if uu____8981
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____8990 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____8990 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____8998 =
                            let uu____8999 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____8999 in
                          giveup_or_defer1 orig uu____8998
                        else
                          (let uu____9001 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____9001
                           then
                             let uu____9002 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____9002
                              then
                                let uu____9003 = subterms args_lhs in
                                imitate' orig env wl1 uu____9003
                              else
                                ((let uu____9007 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____9007
                                  then
                                    let uu____9008 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____9009 = names_to_string fvs1 in
                                    let uu____9010 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9008 uu____9009 uu____9010
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9015 ->
                                        let uu____9016 = sn_binders env vars in
                                        u_abs k_uv uu____9016 t21 in
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
                               (let uu____9025 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____9025
                                then
                                  ((let uu____9027 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____9027
                                    then
                                      let uu____9028 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____9029 = names_to_string fvs1 in
                                      let uu____9030 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9028 uu____9029 uu____9030
                                    else ());
                                   (let uu____9032 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9032
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
                     (let uu____9043 =
                        let uu____9044 = FStar_Syntax_Free.names t1 in
                        check_head uu____9044 t2 in
                      if uu____9043
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____9048 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____9048
                          then
                            let uu____9049 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9049
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9052 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9052 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9094 =
               match uu____9094 with
               | (t,u,k,args) ->
                   let uu____9124 = FStar_Syntax_Util.arrow_formals k in
                   (match uu____9124 with
                    | (all_formals,uu____9135) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____9227  ->
                                        match uu____9227 with
                                        | (x,imp) ->
                                            let uu____9234 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____9234, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____9242 = FStar_Syntax_Util.type_u () in
                                match uu____9242 with
                                | (t1,uu____9246) ->
                                    let uu____9247 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    Prims.fst uu____9247 in
                              let uu____9250 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____9250 with
                               | (t',tm_u1) ->
                                   let uu____9257 = destruct_flex_t t' in
                                   (match uu____9257 with
                                    | (uu____9277,u1,k1,uu____9280) ->
                                        let sol =
                                          let uu____9308 =
                                            let uu____9313 =
                                              u_abs k all_formals t' in
                                            ((u, k), uu____9313) in
                                          TERM uu____9308 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k1, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____9373 = pat_var_opt env pat_args hd1 in
                              (match uu____9373 with
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
                                              (fun uu____9402  ->
                                                 match uu____9402 with
                                                 | (x,uu____9406) ->
                                                     FStar_Syntax_Syntax.bv_eq
                                                       x (Prims.fst y))) in
                                   if Prims.op_Negation maybe_pat
                                   then
                                     aux pat_args pattern_vars
                                       pattern_var_set formals1 tl1
                                   else
                                     (let fvs =
                                        FStar_Syntax_Free.names
                                          (Prims.fst y).FStar_Syntax_Syntax.sort in
                                      let uu____9412 =
                                        let uu____9413 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____9413 in
                                      if uu____9412
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____9417 =
                                           FStar_Util.set_add
                                             (Prims.fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____9417 formals1
                                           tl1)))
                          | uu____9423 -> failwith "Impossible" in
                        let uu____9434 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____9434 all_formals args) in
             let solve_both_pats wl1 uu____9482 uu____9483 r =
               match (uu____9482, uu____9483) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____9637 =
                     (FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys) in
                   if uu____9637
                   then
                     let uu____9641 = solve_prob orig None [] wl1 in
                     solve env uu____9641
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____9656 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____9656
                       then
                         let uu____9657 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____9658 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____9659 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____9660 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____9661 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____9657 uu____9658 uu____9659 uu____9660
                           uu____9661
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____9703 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____9703 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____9711 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____9711 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____9741 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____9741 in
                                  let uu____9744 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____9744 k3)
                           else
                             (let uu____9747 =
                                let uu____9748 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____9749 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____9750 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____9748 uu____9749 uu____9750 in
                              failwith uu____9747) in
                       let uu____9751 =
                         let uu____9757 =
                           let uu____9765 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____9765 in
                         match uu____9757 with
                         | (bs,k1') ->
                             let uu____9783 =
                               let uu____9791 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____9791 in
                             (match uu____9783 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____9812 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_58  ->
                                         FStar_TypeChecker_Common.TProb _0_58)
                                      uu____9812 in
                                  let uu____9817 =
                                    let uu____9820 =
                                      let uu____9821 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____9821.FStar_Syntax_Syntax.n in
                                    let uu____9824 =
                                      let uu____9825 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____9825.FStar_Syntax_Syntax.n in
                                    (uu____9820, uu____9824) in
                                  (match uu____9817 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____9833,uu____9834) ->
                                       (k1', [sub_prob])
                                   | (uu____9838,FStar_Syntax_Syntax.Tm_type
                                      uu____9839) -> (k2', [sub_prob])
                                   | uu____9843 ->
                                       let uu____9846 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____9846 with
                                        | (t,uu____9855) ->
                                            let uu____9856 = new_uvar r zs t in
                                            (match uu____9856 with
                                             | (k_zs,uu____9865) ->
                                                 let kprob =
                                                   let uu____9867 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_59  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_59) uu____9867 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____9751 with
                       | (k_u',sub_probs) ->
                           let uu____9881 =
                             let uu____9889 =
                               let uu____9890 = new_uvar r zs k_u' in
                               FStar_All.pipe_left Prims.fst uu____9890 in
                             let uu____9895 =
                               let uu____9898 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____9898 in
                             let uu____9901 =
                               let uu____9904 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____9904 in
                             (uu____9889, uu____9895, uu____9901) in
                           (match uu____9881 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____9923 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____9923 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____9947 =
                                          FStar_Unionfind.equivalent u1 u2 in
                                        if uu____9947
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____9954 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____9954 with
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
             let solve_one_pat uu____10006 uu____10007 =
               match (uu____10006, uu____10007) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10111 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____10111
                     then
                       let uu____10112 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10113 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10112 uu____10113
                     else ());
                    (let uu____10115 = FStar_Unionfind.equivalent u1 u2 in
                     if uu____10115
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10125  ->
                              fun uu____10126  ->
                                match (uu____10125, uu____10126) with
                                | ((a,uu____10136),(t21,uu____10138)) ->
                                    let uu____10143 =
                                      let uu____10146 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____10146
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____10143
                                      (fun _0_60  ->
                                         FStar_TypeChecker_Common.TProb _0_60))
                           xs args2 in
                       let guard =
                         let uu____10150 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p) Prims.fst)
                             sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____10150 in
                       let wl1 = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____10160 = occurs_check env wl (u1, k1) t21 in
                        match uu____10160 with
                        | (occurs_ok,uu____10169) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____10174 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____10174
                            then
                              let sol =
                                let uu____10176 =
                                  let uu____10181 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____10181) in
                                TERM uu____10176 in
                              let wl1 = solve_prob orig None [sol] wl in
                              solve env wl1
                            else
                              (let uu____10194 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____10194
                               then
                                 let uu____10195 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____10195 with
                                 | (sol,(uu____10209,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____10219 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____10219
                                       then
                                         let uu____10220 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10220
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10225 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____10227 = lhs in
             match uu____10227 with
             | (t1,u1,k1,args1) ->
                 let uu____10232 = rhs in
                 (match uu____10232 with
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
                       | uu____10258 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____10264 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____10264 with
                              | (sol,uu____10271) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____10274 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____10274
                                    then
                                      let uu____10275 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____10275
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____10280 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____10282 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____10282
        then
          let uu____10283 = solve_prob orig None [] wl in
          solve env uu____10283
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____10287 = FStar_Util.physical_equality t1 t2 in
           if uu____10287
           then
             let uu____10288 = solve_prob orig None [] wl in
             solve env uu____10288
           else
             ((let uu____10291 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____10291
               then
                 let uu____10292 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____10292
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar _,_)
                 |(_,FStar_Syntax_Syntax.Tm_bvar _) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___133_10338 =
                     match uu___133_10338 with
                     | [] -> c
                     | bs ->
                         let uu____10352 =
                           (FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))) None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____10352 in
                   let uu____10366 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____10366 with
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
                                   let uu____10452 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____10452
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____10454 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.CProb _0_61)
                                   uu____10454))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___134_10531 =
                     match uu___134_10531 with
                     | [] -> t
                     | bs ->
                         (FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs (bs, t, l))) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____10570 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____10570 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____10653 =
                                   let uu____10656 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____10657 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____10656
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____10657 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_TypeChecker_Common.TProb _0_62)
                                   uu____10653))
               | (FStar_Syntax_Syntax.Tm_abs _,_)
                 |(_,FStar_Syntax_Syntax.Tm_abs _) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____10672 -> true
                     | uu____10687 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____10715 =
                     let uu____10726 = maybe_eta t1 in
                     let uu____10731 = maybe_eta t2 in
                     (uu____10726, uu____10731) in
                   (match uu____10715 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___167_10762 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___167_10762.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___167_10762.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___167_10762.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___167_10762.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___167_10762.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___167_10762.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___167_10762.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___167_10762.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs)
                      |(FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____10795 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____10795
                        then
                          let uu____10796 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____10796 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____10801 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____10812,FStar_Syntax_Syntax.Tm_refine uu____10813) ->
                   let uu____10822 = as_refinement env wl t1 in
                   (match uu____10822 with
                    | (x1,phi1) ->
                        let uu____10827 = as_refinement env wl t2 in
                        (match uu____10827 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____10833 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_63  ->
                                    FStar_TypeChecker_Common.TProb _0_63)
                                 uu____10833 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____10866 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____10866
                                 (guard_on_element wl problem x11) in
                             let fallback uu____10870 =
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
                                 let uu____10876 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     Prims.fst in
                                 FStar_Syntax_Util.mk_conj uu____10876 impl in
                               let wl1 = solve_prob orig (Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____10883 =
                                   let uu____10886 =
                                     let uu____10887 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____10887 :: (p_scope orig) in
                                   mk_problem uu____10886 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____10883 in
                               let uu____10890 =
                                 solve env1
                                   (let uu___168_10891 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___168_10891.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___168_10891.smt_ok);
                                      tcenv = (uu___168_10891.tcenv)
                                    }) in
                               (match uu____10890 with
                                | Failed uu____10895 -> fallback ()
                                | Success uu____10898 ->
                                    let guard =
                                      let uu____10902 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob) Prims.fst in
                                      let uu____10905 =
                                        let uu____10906 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob) Prims.fst in
                                        FStar_All.pipe_right uu____10906
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____10902
                                        uu____10905 in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl2 =
                                      let uu___169_10913 = wl1 in
                                      {
                                        attempting =
                                          (uu___169_10913.attempting);
                                        wl_deferred =
                                          (uu___169_10913.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___169_10913.defer_ok);
                                        smt_ok = (uu___169_10913.smt_ok);
                                        tcenv = (uu___169_10913.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar _,FStar_Syntax_Syntax.Tm_uvar
                  _)
                 |(FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_),FStar_Syntax_Syntax.Tm_uvar
                   _)
                  |(FStar_Syntax_Syntax.Tm_uvar _,FStar_Syntax_Syntax.Tm_app
                    ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                       FStar_Syntax_Syntax.tk = _;
                       FStar_Syntax_Syntax.pos = _;
                       FStar_Syntax_Syntax.vars = _;_},_))
                   |(FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                        FStar_Syntax_Syntax.tk = _;
                        FStar_Syntax_Syntax.pos = _;
                        FStar_Syntax_Syntax.vars = _;_},_),FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                        FStar_Syntax_Syntax.tk = _;
                        FStar_Syntax_Syntax.pos = _;
                        FStar_Syntax_Syntax.vars = _;_},_))
                   ->
                   let uu____10967 = destruct_flex_t t1 in
                   let uu____10968 = destruct_flex_t t2 in
                   flex_flex1 orig uu____10967 uu____10968
               | (FStar_Syntax_Syntax.Tm_uvar _,_)
                 |(FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_),_)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____10984 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____10984 t2 wl
               | (_,FStar_Syntax_Syntax.Tm_uvar _)
                 |(_,FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar _,FStar_Syntax_Syntax.Tm_type
                  _)
                 |(FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_),FStar_Syntax_Syntax.Tm_type
                   _)
                  |(FStar_Syntax_Syntax.Tm_uvar
                    _,FStar_Syntax_Syntax.Tm_arrow _)
                   |(FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                        FStar_Syntax_Syntax.tk = _;
                        FStar_Syntax_Syntax.pos = _;
                        FStar_Syntax_Syntax.vars = _;_},_),FStar_Syntax_Syntax.Tm_arrow
                     _)
                   ->
                   solve_t' env
                     (let uu___170_11033 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___170_11033.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___170_11033.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___170_11033.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___170_11033.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___170_11033.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___170_11033.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___170_11033.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___170_11033.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___170_11033.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar _,_)
                 |(FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_),_)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____11051 =
                        let uu____11052 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____11052 in
                      if uu____11051
                      then
                        let uu____11053 =
                          FStar_All.pipe_left
                            (fun _0_65  ->
                               FStar_TypeChecker_Common.TProb _0_65)
                            (let uu___171_11056 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_11056.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___171_11056.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_11056.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_11056.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_11056.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___171_11056.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_11056.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_11056.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_11056.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____11057 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____11053 uu____11057 t2
                          wl
                      else
                        (let uu____11062 = base_and_refinement env wl t2 in
                         match uu____11062 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____11092 =
                                    FStar_All.pipe_left
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66)
                                      (let uu___172_11095 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___172_11095.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___172_11095.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___172_11095.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___172_11095.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___172_11095.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___172_11095.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___172_11095.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___172_11095.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___172_11095.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____11096 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____11092
                                    uu____11096 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___173_11111 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___173_11111.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___173_11111.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____11114 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67)
                                      uu____11114 in
                                  let guard =
                                    let uu____11122 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob) Prims.fst in
                                    FStar_Syntax_Util.mk_conj uu____11122
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (_,FStar_Syntax_Syntax.Tm_uvar _)
                 |(_,FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____11144 = base_and_refinement env wl t1 in
                      match uu____11144 with
                      | (t_base,uu____11155) ->
                          solve_t env
                            (let uu___174_11170 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___174_11170.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___174_11170.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___174_11170.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___174_11170.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___174_11170.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___174_11170.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___174_11170.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___174_11170.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____11173,uu____11174) ->
                   let t21 =
                     let uu____11182 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____11182 in
                   solve_t env
                     (let uu___175_11195 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_11195.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___175_11195.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___175_11195.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___175_11195.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_11195.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_11195.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_11195.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_11195.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_11195.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____11196,FStar_Syntax_Syntax.Tm_refine uu____11197) ->
                   let t11 =
                     let uu____11205 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____11205 in
                   solve_t env
                     (let uu___176_11218 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_11218.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___176_11218.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___176_11218.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___176_11218.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_11218.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_11218.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_11218.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_11218.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_11218.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match _,_)
                 |(FStar_Syntax_Syntax.Tm_uinst _,_)
                  |(FStar_Syntax_Syntax.Tm_name _,_)
                   |(FStar_Syntax_Syntax.Tm_constant _,_)
                    |(FStar_Syntax_Syntax.Tm_fvar _,_)
                     |(FStar_Syntax_Syntax.Tm_app _,_)
                      |(_,FStar_Syntax_Syntax.Tm_match _)
                       |(_,FStar_Syntax_Syntax.Tm_uinst _)
                        |(_,FStar_Syntax_Syntax.Tm_name _)
                         |(_,FStar_Syntax_Syntax.Tm_constant _)
                          |(_,FStar_Syntax_Syntax.Tm_fvar _)
                           |(_,FStar_Syntax_Syntax.Tm_app _)
                   ->
                   let head1 =
                     let uu____11248 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____11248 Prims.fst in
                   let head2 =
                     let uu____11279 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____11279 Prims.fst in
                   let uu____11307 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____11307
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____11316 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____11316
                      then
                        let guard =
                          let uu____11323 =
                            let uu____11324 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____11324 = FStar_Syntax_Util.Equal in
                          if uu____11323
                          then None
                          else
                            (let uu____11327 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_68  -> Some _0_68)
                               uu____11327) in
                        let uu____11329 = solve_prob orig guard [] wl in
                        solve env uu____11329
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____11333,uu____11334),uu____11335) ->
                   solve_t' env
                     (let uu___177_11364 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___177_11364.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___177_11364.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___177_11364.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___177_11364.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___177_11364.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___177_11364.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___177_11364.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___177_11364.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___177_11364.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____11367,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____11369,uu____11370)) ->
                   solve_t' env
                     (let uu___178_11399 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___178_11399.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___178_11399.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___178_11399.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___178_11399.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___178_11399.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___178_11399.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___178_11399.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___178_11399.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___178_11399.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let _,_)
                 |(FStar_Syntax_Syntax.Tm_meta _,_)
                  |(FStar_Syntax_Syntax.Tm_delayed _,_)
                   |(_,FStar_Syntax_Syntax.Tm_meta _)
                    |(_,FStar_Syntax_Syntax.Tm_delayed _)
                     |(_,FStar_Syntax_Syntax.Tm_let _)
                   ->
                   let uu____11412 =
                     let uu____11413 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____11414 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____11413
                       uu____11414 in
                   failwith uu____11412
               | uu____11415 -> giveup env "head tag mismatch" orig)))
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
          (let uu____11447 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____11447
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____11455  ->
                  fun uu____11456  ->
                    match (uu____11455, uu____11456) with
                    | ((a1,uu____11466),(a2,uu____11468)) ->
                        let uu____11473 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_69  -> FStar_TypeChecker_Common.TProb _0_69)
                          uu____11473)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____11479 =
               FStar_List.map
                 (fun p  -> FStar_All.pipe_right (p_guard p) Prims.fst)
                 sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____11479 in
           let wl1 = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____11499 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____11506)::[] -> wp1
              | uu____11519 ->
                  let uu____11525 =
                    let uu____11526 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____11526 in
                  failwith uu____11525 in
            let uu____11529 =
              let uu____11535 =
                let uu____11536 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____11536 in
              [uu____11535] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____11529;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____11537 = lift_c1 () in solve_eq uu____11537 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___135_11541  ->
                       match uu___135_11541 with
                       | FStar_Syntax_Syntax.TOTAL 
                         |FStar_Syntax_Syntax.MLEFFECT 
                          |FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____11542 -> false)) in
             let uu____11543 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____11567)::uu____11568,(wp2,uu____11570)::uu____11571)
                   -> (wp1, wp2)
               | uu____11612 ->
                   let uu____11625 =
                     let uu____11626 =
                       let uu____11629 =
                         let uu____11630 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____11631 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____11630 uu____11631 in
                       (uu____11629, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____11626 in
                   Prims.raise uu____11625 in
             match uu____11543 with
             | (wpc1,wpc2) ->
                 let uu____11648 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____11648
                 then
                   let uu____11651 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env uu____11651 wl
                 else
                   (let uu____11655 =
                      let uu____11659 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____11659 in
                    match uu____11655 with
                    | (c2_decl,qualifiers) ->
                        let uu____11671 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____11671
                        then
                          let c1_repr =
                            let uu____11674 =
                              let uu____11675 =
                                let uu____11676 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____11676 in
                              let uu____11677 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____11675 uu____11677 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____11674 in
                          let c2_repr =
                            let uu____11679 =
                              let uu____11680 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____11681 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____11680 uu____11681 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____11679 in
                          let prob =
                            let uu____11683 =
                              let uu____11686 =
                                let uu____11687 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____11688 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____11687
                                  uu____11688 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____11686 in
                            FStar_TypeChecker_Common.TProb uu____11683 in
                          let wl1 =
                            let uu____11690 =
                              let uu____11692 =
                                FStar_All.pipe_right (p_guard prob) Prims.fst in
                              Some uu____11692 in
                            solve_prob orig uu____11690 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____11699 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____11699
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____11701 =
                                     let uu____11704 =
                                       let uu____11705 =
                                         let uu____11715 =
                                           let uu____11716 =
                                             let uu____11717 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____11717] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____11716 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____11718 =
                                           let uu____11720 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____11721 =
                                             let uu____11723 =
                                               let uu____11724 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____11724 in
                                             [uu____11723] in
                                           uu____11720 :: uu____11721 in
                                         (uu____11715, uu____11718) in
                                       FStar_Syntax_Syntax.Tm_app uu____11705 in
                                     FStar_Syntax_Syntax.mk uu____11704 in
                                   uu____11701
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____11735 =
                                    let uu____11738 =
                                      let uu____11739 =
                                        let uu____11749 =
                                          let uu____11750 =
                                            let uu____11751 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____11751] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____11750 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____11752 =
                                          let uu____11754 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____11755 =
                                            let uu____11757 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____11758 =
                                              let uu____11760 =
                                                let uu____11761 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____11761 in
                                              [uu____11760] in
                                            uu____11757 :: uu____11758 in
                                          uu____11754 :: uu____11755 in
                                        (uu____11749, uu____11752) in
                                      FStar_Syntax_Syntax.Tm_app uu____11739 in
                                    FStar_Syntax_Syntax.mk uu____11738 in
                                  uu____11735
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____11772 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_70  ->
                                  FStar_TypeChecker_Common.TProb _0_70)
                               uu____11772 in
                           let wl1 =
                             let uu____11778 =
                               let uu____11780 =
                                 let uu____11783 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     Prims.fst in
                                 FStar_Syntax_Util.mk_conj uu____11783 g in
                               FStar_All.pipe_left (fun _0_71  -> Some _0_71)
                                 uu____11780 in
                             solve_prob orig uu____11778 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____11793 = FStar_Util.physical_equality c1 c2 in
        if uu____11793
        then
          let uu____11794 = solve_prob orig None [] wl in
          solve env uu____11794
        else
          ((let uu____11797 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____11797
            then
              let uu____11798 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____11799 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____11798
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____11799
            else ());
           (let uu____11801 =
              let uu____11804 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____11805 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____11804, uu____11805) in
            match uu____11801 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____11809),FStar_Syntax_Syntax.Total
                    (t2,uu____11811)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____11824 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____11824 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____11827,FStar_Syntax_Syntax.Total uu____11828) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,_),FStar_Syntax_Syntax.Total (t2,_))
                   |(FStar_Syntax_Syntax.GTotal
                     (t1,_),FStar_Syntax_Syntax.GTotal (t2,_))
                    |(FStar_Syntax_Syntax.Total
                      (t1,_),FStar_Syntax_Syntax.GTotal (t2,_))
                     ->
                     let uu____11877 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____11877 wl
                 | (FStar_Syntax_Syntax.GTotal _,FStar_Syntax_Syntax.Comp _)
                   |(FStar_Syntax_Syntax.Total _,FStar_Syntax_Syntax.Comp _)
                     ->
                     let uu____11884 =
                       let uu___179_11887 = problem in
                       let uu____11890 =
                         let uu____11891 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____11891 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_11887.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____11890;
                         FStar_TypeChecker_Common.relation =
                           (uu___179_11887.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___179_11887.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___179_11887.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_11887.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_11887.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_11887.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_11887.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_11887.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____11884 wl
                 | (FStar_Syntax_Syntax.Comp _,FStar_Syntax_Syntax.GTotal _)
                   |(FStar_Syntax_Syntax.Comp _,FStar_Syntax_Syntax.Total _)
                     ->
                     let uu____11896 =
                       let uu___180_11899 = problem in
                       let uu____11902 =
                         let uu____11903 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____11903 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___180_11899.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___180_11899.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___180_11899.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____11902;
                         FStar_TypeChecker_Common.element =
                           (uu___180_11899.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___180_11899.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___180_11899.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___180_11899.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___180_11899.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___180_11899.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____11896 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____11904,FStar_Syntax_Syntax.Comp uu____11905) ->
                     let uu____11906 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____11906
                     then
                       let uu____11907 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type" in
                       solve_t env uu____11907 wl
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
                           (let uu____11917 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____11917
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____11919 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____11919 with
                            | None  ->
                                let uu____11921 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____11922 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____11922) in
                                if uu____11921
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
                                  (let uu____11925 =
                                     let uu____11926 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____11927 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____11926 uu____11927 in
                                   giveup env uu____11925 orig)
                            | Some edge -> solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____11932 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____11952  ->
              match uu____11952 with
              | (uu____11963,uu____11964,u,uu____11966,uu____11967,uu____11968)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____11932 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____11997 =
        FStar_All.pipe_right (Prims.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____11997 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____12007 =
        FStar_All.pipe_right (Prims.snd ineqs)
          (FStar_List.map
             (fun uu____12019  ->
                match uu____12019 with
                | (u1,u2) ->
                    let uu____12024 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____12025 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____12024 uu____12025)) in
      FStar_All.pipe_right uu____12007 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____12037,[])) -> "{}"
      | uu____12050 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____12060 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____12060
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____12063 =
              FStar_List.map
                (fun uu____12067  ->
                   match uu____12067 with
                   | (uu____12070,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____12063 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____12074 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____12074 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____12112 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____12112
    then
      let uu____12113 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____12114 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____12113
        (rel_to_string rel) uu____12114
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
            let uu____12134 =
              let uu____12136 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_72  -> Some _0_72) uu____12136 in
            FStar_Syntax_Syntax.new_bv uu____12134 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____12142 =
              let uu____12144 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_73  -> Some _0_73) uu____12144 in
            let uu____12146 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____12142 uu____12146 in
          ((FStar_TypeChecker_Common.TProb p), x)
let solve_and_commit:
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob* Prims.string) ->
         FStar_TypeChecker_Common.deferred Prims.option)
        -> FStar_TypeChecker_Common.deferred Prims.option
  =
  fun env  ->
    fun probs  ->
      fun err1  ->
        let probs1 =
          let uu____12169 = FStar_Options.eager_inference () in
          if uu____12169
          then
            let uu___181_12170 = probs in
            {
              attempting = (uu___181_12170.attempting);
              wl_deferred = (uu___181_12170.wl_deferred);
              ctr = (uu___181_12170.ctr);
              defer_ok = false;
              smt_ok = (uu___181_12170.smt_ok);
              tcenv = (uu___181_12170.tcenv)
            }
          else probs in
        let tx = FStar_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred -> (FStar_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Unionfind.rollback tx;
             (let uu____12181 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____12181
              then
                let uu____12182 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____12182
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
          ((let uu____12192 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____12192
            then
              let uu____12193 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____12193
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____12197 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____12197
             then
               let uu____12198 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____12198
             else ());
            (let f2 =
               let uu____12201 =
                 let uu____12202 = FStar_Syntax_Util.unmeta f1 in
                 uu____12202.FStar_Syntax_Syntax.n in
               match uu____12201 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____12206 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___182_12207 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___182_12207.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___182_12207.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___182_12207.FStar_TypeChecker_Env.implicits)
             })))
let with_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_TypeChecker_Common.deferred Prims.option ->
        FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | None  -> None
        | Some d ->
            let uu____12222 =
              let uu____12223 =
                let uu____12224 =
                  let uu____12225 =
                    FStar_All.pipe_right (p_guard prob) Prims.fst in
                  FStar_All.pipe_right uu____12225
                    (fun _0_74  -> FStar_TypeChecker_Common.NonTrivial _0_74) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____12224;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____12223 in
            FStar_All.pipe_left (fun _0_75  -> Some _0_75) uu____12222
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____12258 =
        let uu____12259 =
          let uu____12260 = FStar_All.pipe_right (p_guard prob) Prims.fst in
          FStar_All.pipe_right uu____12260
            (fun _0_76  -> FStar_TypeChecker_Common.NonTrivial _0_76) in
        {
          FStar_TypeChecker_Env.guard_f = uu____12259;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      Some uu____12258
let try_teq:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____12286 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____12286
           then
             let uu____12287 = FStar_Syntax_Print.term_to_string t1 in
             let uu____12288 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____12287
               uu____12288
           else ());
          (let prob =
             let uu____12291 =
               let uu____12294 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____12294 in
             FStar_All.pipe_left
               (fun _0_77  -> FStar_TypeChecker_Common.TProb _0_77)
               uu____12291 in
           let g =
             let uu____12299 =
               let uu____12301 = singleton' env prob smt_ok in
               solve_and_commit env uu____12301 (fun uu____12302  -> None) in
             FStar_All.pipe_left (with_guard env prob) uu____12299 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____12316 = try_teq true env t1 t2 in
        match uu____12316 with
        | None  ->
            let uu____12318 =
              let uu____12319 =
                let uu____12322 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                let uu____12323 = FStar_TypeChecker_Env.get_range env in
                (uu____12322, uu____12323) in
              FStar_Errors.Error uu____12319 in
            Prims.raise uu____12318
        | Some g ->
            ((let uu____12326 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____12326
              then
                let uu____12327 = FStar_Syntax_Print.term_to_string t1 in
                let uu____12328 = FStar_Syntax_Print.term_to_string t2 in
                let uu____12329 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____12327
                  uu____12328 uu____12329
              else ());
             g)
let try_subtype':
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        Prims.bool -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun smt_ok  ->
          (let uu____12345 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____12345
           then
             let uu____12346 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____12347 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____12346
               uu____12347
           else ());
          (let uu____12349 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____12349 with
           | (prob,x) ->
               let g =
                 let uu____12357 =
                   let uu____12359 = singleton' env prob smt_ok in
                   solve_and_commit env uu____12359
                     (fun uu____12360  -> None) in
                 FStar_All.pipe_left (with_guard env prob) uu____12357 in
               ((let uu____12366 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____12366
                 then
                   let uu____12367 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____12368 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____12369 =
                     let uu____12370 = FStar_Util.must g in
                     guard_to_string env uu____12370 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____12367 uu____12368 uu____12369
                 else ());
                abstract_guard x g))
let try_subtype:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t Prims.option
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
          let uu____12394 = FStar_TypeChecker_Env.get_range env in
          let uu____12395 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.err uu____12394 uu____12395
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____12407 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____12407
         then
           let uu____12408 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____12409 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____12408
             uu____12409
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____12414 =
             let uu____12417 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None uu____12417 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_78  -> FStar_TypeChecker_Common.CProb _0_78) uu____12414 in
         let uu____12420 =
           let uu____12422 = singleton env prob in
           solve_and_commit env uu____12422 (fun uu____12423  -> None) in
         FStar_All.pipe_left (with_guard env prob) uu____12420)
let solve_universe_inequalities':
  FStar_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____12442  ->
        match uu____12442 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Unionfind.rollback tx;
              (let uu____12467 =
                 let uu____12468 =
                   let uu____12471 =
                     let uu____12472 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____12473 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____12472 uu____12473 in
                   let uu____12474 = FStar_TypeChecker_Env.get_range env in
                   (uu____12471, uu____12474) in
                 FStar_Errors.Error uu____12468 in
               Prims.raise uu____12467) in
            let equiv v1 v' =
              let uu____12482 =
                let uu____12485 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____12486 = FStar_Syntax_Subst.compress_univ v' in
                (uu____12485, uu____12486) in
              match uu____12482 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Unionfind.equivalent v0 v0'
              | uu____12494 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____12508 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____12508 with
                      | FStar_Syntax_Syntax.U_unif uu____12512 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____12523  ->
                                    match uu____12523 with
                                    | (u,v') ->
                                        let uu____12529 = equiv v1 v' in
                                        if uu____12529
                                        then
                                          let uu____12531 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____12531 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____12541 -> [])) in
            let uu____12544 =
              let wl =
                let uu___183_12547 = empty_worklist env in
                {
                  attempting = (uu___183_12547.attempting);
                  wl_deferred = (uu___183_12547.wl_deferred);
                  ctr = (uu___183_12547.ctr);
                  defer_ok = false;
                  smt_ok = (uu___183_12547.smt_ok);
                  tcenv = (uu___183_12547.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____12554  ->
                      match uu____12554 with
                      | (lb,v1) ->
                          let uu____12559 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____12559 with
                           | USolved wl1 -> ()
                           | uu____12561 -> fail lb v1))) in
            let rec check_ineq uu____12567 =
              match uu____12567 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____12574) -> true
                   | (FStar_Syntax_Syntax.U_succ
                      u0,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name
                      u0,FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif
                      u0,FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Unionfind.equivalent u0 v0
                   | (FStar_Syntax_Syntax.U_name _,FStar_Syntax_Syntax.U_succ
                      v0)
                     |(FStar_Syntax_Syntax.U_unif
                       _,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____12590) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____12594,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____12599 -> false) in
            let uu____12602 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____12608  ->
                      match uu____12608 with
                      | (u,v1) ->
                          let uu____12613 = check_ineq (u, v1) in
                          if uu____12613
                          then true
                          else
                            ((let uu____12616 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____12616
                              then
                                let uu____12617 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____12618 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____12617
                                  uu____12618
                              else ());
                             false))) in
            if uu____12602
            then ()
            else
              ((let uu____12622 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____12622
                then
                  ((let uu____12624 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____12624);
                   FStar_Unionfind.rollback tx;
                   (let uu____12630 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____12630))
                else ());
               (let uu____12636 =
                  let uu____12637 =
                    let uu____12640 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____12640) in
                  FStar_Errors.Error uu____12637 in
                Prims.raise uu____12636))
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
      let fail uu____12673 =
        match uu____12673 with
        | (d,s) ->
            let msg = explain env d s in
            Prims.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____12683 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____12683
       then
         let uu____12684 = wl_to_string wl in
         let uu____12685 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____12684 uu____12685
       else ());
      (let g1 =
         let uu____12697 = solve_and_commit env wl fail in
         match uu____12697 with
         | Some [] ->
             let uu___184_12704 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___184_12704.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___184_12704.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___184_12704.FStar_TypeChecker_Env.implicits)
             }
         | uu____12707 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___185_12710 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___185_12710.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___185_12710.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___185_12710.FStar_TypeChecker_Env.implicits)
        }))
let discharge_guard':
  (Prims.unit -> Prims.string) Prims.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let g1 = solve_deferred_constraints env g in
          let ret_g =
            let uu___186_12736 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___186_12736.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___186_12736.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___186_12736.FStar_TypeChecker_Env.implicits)
            } in
          let uu____12737 =
            let uu____12738 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____12738 in
          if uu____12737
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____12744 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____12744
                   then
                     let uu____12745 = FStar_TypeChecker_Env.get_range env in
                     let uu____12746 =
                       let uu____12747 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____12747 in
                     FStar_Errors.diag uu____12745 uu____12746
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
                         ((let uu____12756 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____12756
                           then
                             let uu____12757 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____12758 =
                               let uu____12759 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____12759 in
                             FStar_Errors.diag uu____12757 uu____12758
                           else ());
                          (let vcs =
                             let uu____12765 = FStar_Options.use_tactics () in
                             if uu____12765
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)] in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____12779  ->
                                   match uu____12779 with
                                   | (env1,goal) ->
                                       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                         use_env_range_msg env1 goal)));
                          Some ret_g))))
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____12790 = discharge_guard' None env g true in
      match uu____12790 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____12810 = FStar_Unionfind.find u in
      match uu____12810 with
      | FStar_Syntax_Syntax.Uvar  -> true
      | uu____12819 -> false in
    let rec until_fixpoint acc implicits =
      let uu____12834 = acc in
      match uu____12834 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____12880 = hd1 in
               (match uu____12880 with
                | (uu____12887,env,u,tm,k,r) ->
                    let uu____12893 = unresolved u in
                    if uu____12893
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm in
                       (let uu____12911 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck") in
                        if uu____12911
                        then
                          let uu____12912 =
                            FStar_Syntax_Print.uvar_to_string u in
                          let uu____12916 =
                            FStar_Syntax_Print.term_to_string tm1 in
                          let uu____12917 =
                            FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____12912 uu____12916 uu____12917
                        else ());
                       (let uu____12919 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___187_12923 = env1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___187_12923.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___187_12923.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___187_12923.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___187_12923.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___187_12923.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___187_12923.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___187_12923.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___187_12923.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___187_12923.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___187_12923.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___187_12923.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___187_12923.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___187_12923.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___187_12923.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___187_12923.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___187_12923.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___187_12923.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___187_12923.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___187_12923.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___187_12923.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___187_12923.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___187_12923.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___187_12923.FStar_TypeChecker_Env.qname_and_index)
                             }) tm1 in
                        match uu____12919 with
                        | (uu____12924,uu____12925,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___188_12928 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___188_12928.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___188_12928.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___188_12928.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____12931 =
                                discharge_guard'
                                  (Some
                                     (fun uu____12935  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____12931 with
                              | Some g3 -> g3
                              | None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
    let uu___189_12950 = g in
    let uu____12951 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___189_12950.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___189_12950.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___189_12950.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____12951
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____12979 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____12979 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____12986 = discharge_guard env g1 in
          FStar_All.pipe_left Prims.ignore uu____12986
      | (reason,uu____12988,uu____12989,e,t,r)::uu____12993 ->
          let uu____13007 =
            let uu____13008 = FStar_Syntax_Print.term_to_string t in
            let uu____13009 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format3
              "Failed to resolve implicit argument of type '%s' introduced in %s because %s"
              uu____13008 uu____13009 reason in
          FStar_Errors.err r uu____13007
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___190_13016 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___190_13016.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___190_13016.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___190_13016.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____13034 = try_teq false env t1 t2 in
        match uu____13034 with
        | None  -> false
        | Some g ->
            let uu____13037 = discharge_guard' None env g false in
            (match uu____13037 with
             | Some uu____13041 -> true
             | None  -> false)